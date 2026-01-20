import os
import sys
import threading
from contextlib import contextmanager

from PySide6.QtCore    import Qt, QObject, Signal, QThread
from PySide6.QtWidgets import (
    QApplication,
    QMainWindow,
    QComboBox,
    QFileDialog,
    QMessageBox,
    QTextBrowser,
    QWidget,
)
from PySide6.QtCore import QTimer
import math
import serial
import serial.tools.list_ports
import struct
import time
import resources_rc
from PySide6.QtGui import QIcon

from ui_main import Ui_MainWindow

# --- константы для обновления ---
FUNC_CODE_FIRMWARE = 0x2A
FUNC_CODE_START    = 0x2B
BOOTLOADER_ID      = 1

MAX_PACKET_SIZE    = 91
HEADER_SIZE        = 5
CRC_SIZE           = 2
MAX_PAYLOAD_SIZE   = MAX_PACKET_SIZE - HEADER_SIZE - CRC_SIZE

MAX_RETRIES        = 3
RETRY_DELAY        = 1

MAX_FIRMWARE_FILE_SIZE = 28 * 1024  # 28 КБ

# --- карта регистров ---------------------------------------------------
# --- карта регистров (новая) ------------------------------------------
REG_MODBUSTIMEOUT = 0x0002  # 2: modbustimeout
REG_BAUD          = 0x0003  # 3: скорость UART * 100 (см. кодирование ниже)
REG_BITS          = 0x0004  # 4: длина слова UART
REG_STOP          = 0x0005  # 5: стоп-бит UART
REG_PARITY        = 0x0006  # 6: чётность
REG_USART_ID      = 0x0007  # 7: UART ID (Modbus slave id)
REG_PASSWORD      = 0x0008  # 8: пароль


# Количество регистров датчиков
SENSOR_REG_COUNT = 9


REG_SENSOR_READ_START= 0x0000
REG_SENSOR_READ_END = 0x0008


# --- настройки USART для автоподключения и отправки 0x2A ---------
# используются при приёме пакета автоподключения и во время
# обновления прошивки
DEFAULT_BAUDRATE = 56000  # скорость по умолчанию для автоподключения (115 200 бод)
DEFAULT_BYTESIZE = serial.EIGHTBITS
DEFAULT_PARITY   = serial.PARITY_NONE
DEFAULT_STOPBITS = serial.STOPBITS_ONE

# --- параметры автозапроса настроек -----------------------------------
AUTO_CONNECT_CMD = b"\x41"      # команда, которую нужно слать устройству в режиме автоподключения
AUTO_CONNECT_INTERVAL = 0.2     # период отправки команды 0x41 в секундах (200 мс)
AUTO_CONNECT_RESPONSE_LEN = 15  # ожидаемый размер ответа с настройками (байт)


class AutoConnectWorker(QObject):
    """Поток для приёма Modbus пакета с настройками."""

    finished = Signal(dict)
    error = Signal(str)

    def __init__(self, port: str):
        super().__init__()
        self.port = port
        self._running = True

    def stop(self):
        self._running = False

    def run(self):
        try:
            ser = serial.Serial(
                self.port,
                baudrate=DEFAULT_BAUDRATE,
                bytesize=DEFAULT_BYTESIZE,
                parity=DEFAULT_PARITY,
                stopbits=DEFAULT_STOPBITS,
                timeout=AUTO_CONNECT_INTERVAL,
            )
        except serial.SerialException as exc:
            self.error.emit(str(exc))
            return

        try:
            ser.reset_input_buffer()
        except serial.SerialException:
            pass

        while self._running:
            loop_started = time.monotonic()
            try:
                ser.write(AUTO_CONNECT_CMD)
            except serial.SerialException as exc:
                self.error.emit(str(exc))
                break

            data = ser.read(AUTO_CONNECT_RESPONSE_LEN)
            if len(data) >= AUTO_CONNECT_RESPONSE_LEN and self._check_crc(data):
                settings = self._parse_regs(data)
                ser.close()
                self.finished.emit(settings)
                return

            remaining = AUTO_CONNECT_INTERVAL - (time.monotonic() - loop_started)
            if remaining > 0:
                time.sleep(remaining)

        ser.close()

    # ------ вспомогательные функции ---------------------------------
    @staticmethod
    def _calc_crc(data: bytes) -> int:
        crc = 0xFFFF
        for ch in data:
            crc ^= ch
            for _ in range(8):
                if crc & 1:
                    crc >>= 1
                    crc ^= 0xA001
                else:
                    crc >>= 1
        return crc

    def _check_crc(self, packet: bytes) -> bool:
        recv = int.from_bytes(packet[-2:], byteorder="little")
        calc = self._calc_crc(packet[:-2])
        return recv == calc

    @staticmethod
    def _parse_regs(packet: bytes) -> dict:
        """Декодирует регистры STM32 HAL в формат программы."""
        # данные начинаются после трёх байт заголовка
        regs = [int.from_bytes(packet[3 + i * 2: 5 + i * 2], byteorder="big") for i in range(6)]

        # Декодирование регистров STM32 HAL -> формат программы
        baud_raw = regs[0] * 100  # 560 -> 56000, 1152 -> 115200
        wordlen_raw = regs[1]  # 0x0000=8bit, 0x1000=9bit
        stop_raw = regs[2]  # 0x0000=1, 0x2000=2
        parity_raw = regs[3]  # 0x0000=none, 0x0400=even, 0x0600=odd

        # Преобразование в формат программы
        settings = {
            "baud": baud_raw,  # уже умножено на 100
            "bits": 8 if wordlen_raw == 0x00000000 else 9,
            "parity": 0 if parity_raw == 0x00000000 else \
                2 if parity_raw == 0x00000400 else \
                    1,  # 0=none, 1=odd, 2=even
            "stop": 1 if stop_raw == 0x00000000 else 2,
            "usart_id": regs[4],
        }
        return settings


class RegisterMap:
    """Карта регистров устройства."""

    def __init__(self):
        # Первые 2 регистра (16-bit) разбиваются на байты
        self.errGlobal: int = 0  # регистр 0, младший байт
        self.OsRelay: int = 0  # регистр 0, старший байт
        self.Relay: int = 0  # регистр 1, младший байт
        self.Tumblers: int = 0  # регистр 1, старший байт

        # Остальные регистры целиком (16-bit)
        self.modbustimeout: int = 0  # регистр 2
        self.UARTspeed: int = 0  # регистр 3
        self.UARTwordlen: int = 0  # регистр 4
        self.UARTstopbit: int = 0  # регистр 5
        self.UARTparity: int = 0  # регистр 6
        self.UARTid: int = 0  # регистр 7
        self.Pass: int = 0  # регистр 8

    def update(self, regs: list[int]) -> None:
        """Обновляет поля из массива регистров (минимум 9 элементов)."""
        if len(regs) < 9:
            return

        # Регистр 0: младший и старший байты
        self.errGlobal = regs[0] & 0xFF
        self.OsRelay = (regs[0] >> 8) & 0xFF

        # Регистр 1: младший и старший байты
        self.Relay = regs[1] & 0xFF
        self.Tumblers = (regs[1] >> 8) & 0xFF

        # Регистры 2-8 целиком
        self.modbustimeout = regs[2]
        self.UARTspeed = regs[3]
        self.UARTwordlen = regs[4]
        self.UARTstopbit = regs[5]
        self.UARTparity = regs[6]
        self.UARTid = regs[7]
        self.Pass = regs[8]

    def __repr__(self) -> str:
        return (
            f"RegisterMap(errGlobal={self.errGlobal}, OsRelay={self.OsRelay}, "
            f"Relay={self.Relay}, Tumblers={self.Tumblers}, "
            f"modbustimeout={self.modbustimeout}, UARTspeed={self.UARTspeed}, "
            f"UARTwordlen={self.UARTwordlen}, UARTstopbit={self.UARTstopbit}, "
            f"UARTparity={self.UARTparity}, UARTid={self.UARTid}, Pass={self.Pass})"
        )


# Глобальный экземпляр
device_registers = RegisterMap()



class RegisterPoller(QObject):
    """Поток опроса регистров устройства (просто читаем блок и сохраняем)."""

    data_ready = Signal(list)          # теперь сигнал несёт только считанные регистры
    error = Signal(str)
    connection_lost = Signal()

    def __init__(self, serial_port: serial.Serial, slave_id: int, lock: threading.Lock):
        super().__init__()
        self.serial_port = serial_port
        self.slave_id = slave_id
        self._lock = lock
        self._running = True
        self._fail_count = 0

        self.last_regs: list[int] = [0] * 9  # сюда сохраняем последние 9 регистров
        self.last_regs_ts: float = 0.0       # (опционально) timestamp

    def stop(self):
        self._running = False

    def run(self):
        START_ADDR = 0          # регистр 0
        COUNT = 9               # регистры 0..8

        while self._running:
            try:
                regs = self._read_registers(START_ADDR, COUNT)
                if regs is None:
                    continue

                self._fail_count = 0
                self.last_regs = regs
                self.last_regs_ts = time.time()

                self.data_ready.emit(regs)   # можно убрать, если сигнал не нужен

            except serial.SerialException as exc:
                self.error.emit(str(exc))
                break

            time.sleep(1)

    def _check_crc(self, packet: bytes) -> bool:
        recv = int.from_bytes(packet[-2:], "little")
        calc = AutoConnectWorker._calc_crc(packet[:-2])
        return recv == calc

    def _read_registers(self, start_addr: int, count: int) -> list[int] | None:
        req = struct.pack(">BBHH", self.slave_id, 3, start_addr, count)
        crc = AutoConnectWorker._calc_crc(req)
        try:
            with self._lock:
                self.serial_port.write(req + crc.to_bytes(2, "little"))
                expected_len = 5 + count * 2
                resp = self.serial_port.read(expected_len)
        except serial.SerialException as exc:
            self.error.emit(str(exc))
            self._running = False
            return None
        if len(resp) < expected_len or not self._check_crc(resp):
            if resp:
                # Любой ответ (даже мусор) считаем признаком связи.
                self._fail_count = 0
            else:
                self._fail_count += 1
                if self._fail_count >= 5:
                    self.connection_lost.emit()
                    self._running = False
            time.sleep(1)
            return None
        regs = [int.from_bytes(resp[3 + i * 2 : 5 + i * 2], "big") for i in range(count)]
        return regs


class FirmwareUpdateWorker(QObject):
    """\u041e\u0431\u043d\u043e\u0432\u043b\u0435\u043d\u0438\u0435 \u041f\u041e \u0432 \u043e\u0442\u0434\u0435\u043b\u044c\u043d\u043e\u043c \u043f\u043e\u0442\u043e\u043a\u0435."""

    progress = Signal(int, str)
    finished = Signal(bool)

    def __init__(self, serial_port: serial.Serial, slave_id: int, filename: str, lock: threading.Lock):
        super().__init__()
        self.serial_port = serial_port
        self.slave_id = slave_id
        self.filename = filename
        self._lock = lock
        self._running = True

    def stop(self):
        self._running = False

    # --- \u043f\u0440\u043e\u0446\u0435\u0441\u0441 \u043e\u0431\u043d\u043e\u0432\u043b\u0435\u043d\u0438\u044f ----------------------
    def run(self):
        try:
            with open(self.filename, "rb") as f:
                firmware_data = f.read()
        except Exception:
            self.finished.emit(False)
            return

        total_packets = math.ceil(len(firmware_data) / MAX_PAYLOAD_SIZE)

        # ---- 0x2B ----
        if not self._send_start():
            self.finished.emit(False)
            return

        time.sleep(7)

        # ---- \u0441\u043c\u0435\u043d\u0430 \u043d\u0430 \u0434\u0435\u0444\u043e\u043b\u0442\u043d\u044b\u0435 \u043d\u0430\u0441\u0442\u0440\u043e\u0439\u043a\u0438 ----
        orig_cfg = (
            self.serial_port.baudrate,
            self.serial_port.bytesize,
            self.serial_port.parity,
            self.serial_port.stopbits,
        )
        try:
            # \u043f\u043e\u0441\u043b\u0435 \u043a\u043e\u043c\u0430\u043d\u0434\u044b 0x2B
            # \u043f\u0435\u0440\u0435\u043a\u043b\u044e\u0447\u0430\u0435\u043c \u043f\u043e\u0440\u0442 \u043d\u0430 \u043e\u0431\u0449\u0438\u0435
            # \u043d\u0430\u0441\u0442\u0440\u043e\u0439\u043a\u0438 \u0434\u043b\u044f \u043e\u0442\u043f\u0440\u0430\u0432\u043a\u0438 0x2A
            self.serial_port.baudrate = DEFAULT_BAUDRATE
            self.serial_port.bytesize = DEFAULT_BYTESIZE
            self.serial_port.parity = DEFAULT_PARITY
            self.serial_port.stopbits = DEFAULT_STOPBITS
        except serial.SerialException:
            self.finished.emit(False)
            return

        first_ack = False
        for i in range(total_packets):
            if not self._running:
                self.finished.emit(False)
                return
            chunk = firmware_data[i * MAX_PAYLOAD_SIZE : (i + 1) * MAX_PAYLOAD_SIZE]
            if not self._send_packet(i + 1, total_packets, chunk):
                # \u043e\u0448\u0438\u0431\u043a\u0430 \u043e\u0442\u043f\u0440\u0430\u0432\u043a\u0438
                self._restore_serial(orig_cfg)
                self.finished.emit(False)
                return

            if not first_ack:
                first_ack = True

            pct = int((i + 1) * 100 / total_packets)
            msg = "" if first_ack else "\u043f\u043e\u0434\u0433\u043e\u0442\u043e\u0432\u043a\u0430 \u043a \u043e\u0431\u043d\u043e\u0432\u043b\u0435\u043d\u0438\u044e"
            self.progress.emit(pct, msg)

        self._restore_serial(orig_cfg)
        self.finished.emit(True)

    # ------------------------------------------------------------------
    def _restore_serial(self, cfg):
        try:
            self.serial_port.baudrate = cfg[0]
            self.serial_port.bytesize = cfg[1]
            self.serial_port.parity = cfg[2]
            self.serial_port.stopbits = cfg[3]
        except serial.SerialException:
            pass

    def _send_start(self) -> bool:
        try:
            req = struct.pack(">BB", self.slave_id, FUNC_CODE_START)
            crc = AutoConnectWorker._calc_crc(req)
            with self._lock:
                self.serial_port.write(req + crc.to_bytes(2, "little"))
                resp = self.serial_port.read(8)
            return len(resp) >= 4
        except serial.SerialException:
            return False

    def _send_packet(self, idx: int, total: int, payload: bytes) -> bool:
        frame = bytearray()
        frame += struct.pack(">BB", BOOTLOADER_ID, FUNC_CODE_FIRMWARE)
        frame += idx.to_bytes(2, "big")
        frame += total.to_bytes(2, "big")
        frame += payload
        crc = AutoConnectWorker._calc_crc(frame)
        frame += crc.to_bytes(2, "little")

        for attempt in range(1, MAX_RETRIES + 1):
            try:
                print(f"Пакет {idx}/{total} отправлен (попытка {attempt})")
                with self._lock:
                    self.serial_port.write(frame)
                    resp = self.serial_port.read(8)
                if len(resp) >= 4:
                    print(f"Ответ получен для пакета {idx}/{total}")
                    return True
            except serial.SerialException:
                pass
            time.sleep(RETRY_DELAY)
        return False


class BootloaderUpdateWorker(QObject):
    """Обновление прошивки напрямую из загрузчика (только пакеты 0x2A)."""

    progress = Signal(int, str)
    finished = Signal(bool)

    def __init__(self, port_name: str, filename: str, slave_id: int = BOOTLOADER_ID):
        super().__init__()
        self.port_name = port_name
        self.filename = filename
        self.slave_id = slave_id
        self._running = True

    def stop(self):
        self._running = False

    def run(self):
        try:
            ser = serial.Serial(
                self.port_name,
                baudrate=DEFAULT_BAUDRATE,
                bytesize=DEFAULT_BYTESIZE,
                parity=DEFAULT_PARITY,
                stopbits=DEFAULT_STOPBITS,
                timeout=3,
            )
        except serial.SerialException:
            self.finished.emit(False)
            return

        try:
            with open(self.filename, "rb") as f:
                firmware_data = f.read()
        except Exception:
            ser.close()
            self.finished.emit(False)
            return

        total_packets = math.ceil(len(firmware_data) / MAX_PAYLOAD_SIZE)
        first_ack = False
        for i in range(total_packets):
            if not self._running:
                ser.close()
                self.finished.emit(False)
                return

            chunk = firmware_data[i * MAX_PAYLOAD_SIZE : (i + 1) * MAX_PAYLOAD_SIZE]
            if not self._send_packet(ser, i + 1, total_packets, chunk):
                ser.close()
                self.finished.emit(False)
                return

            if not first_ack:
                first_ack = True

            pct = int((i + 1) * 100 / total_packets)
            msg = "" if first_ack else "подготовка к обновлению"
            self.progress.emit(pct, msg)

        ser.close()
        self.finished.emit(True)

    def _send_packet(self, ser: serial.Serial, idx: int, total: int, payload: bytes) -> bool:
        frame = bytearray()
        frame += struct.pack(">BB", self.slave_id, FUNC_CODE_FIRMWARE)
        frame += idx.to_bytes(2, "big")
        frame += total.to_bytes(2, "big")
        frame += payload
        crc = AutoConnectWorker._calc_crc(frame)
        frame += crc.to_bytes(2, "little")

        for attempt in range(1, MAX_RETRIES + 1):
            try:
                print(f"Пакет {idx}/{total} отправлен (попытка {attempt})")
                ser.write(frame)
                resp = ser.read(8)
                if len(resp) >= 4:
                    print(f"Ответ получен для пакета {idx}/{total}")
                    return True
            except serial.SerialException:
                pass
            time.sleep(RETRY_DELAY)
        return False





from PySide6.QtCore import Signal

class TestLedSequenceWorker(QObject):
    finished = Signal(bool, int, int, list)

    def __init__(self, serial_port, slave_id, low_fill, lock, test_index, parent=None):
        super().__init__(parent)
        self.serial_port = serial_port
        self.slave_id = slave_id
        self.low_fill = low_fill
        self.lock = lock
        self.test_index = test_index
        self.running = True
        self.error_mask = 0
        self.reg0_reads: list[int] = []
        self._feedback_byte_source = "high"

    def stop(self):
        self.running = False

    @staticmethod
    def checkcrc(packet):
        if len(packet) < 2:
            return False
        calc_crc = AutoConnectWorker._calc_crc(packet[:-2])
        recv_crc = int.from_bytes(packet[-2:], 'little')
        return calc_crc == recv_crc

    def run(self):
        for step in range(8):
            if not self.running:
                self.finished.emit(False, self.test_index, self.error_mask, self.reg0_reads)
                return
            low_byte = self.low_fill
            high_byte = 0xFF - (0xFF >> (step + 1))
            coil_data = bytes([ high_byte, low_byte])
            req_head = struct.pack('>BBHHB', self.slave_id, 0x0F, 0, 16, 2)
            req = req_head + coil_data
            crc_val = AutoConnectWorker._calc_crc(req)
            req += struct.pack('<H', crc_val)
            try:
                with self.lock:
                    self.serial_port.reset_input_buffer()
                    self.serial_port.write(req)
                    resp = self.serial_port.read(8)
                if len(resp) != 8 or not self.checkcrc(resp):
                    self.finished.emit(False, self.test_index, self.error_mask, self.reg0_reads)
                    return
            except Exception:
                self.finished.emit(False, self.test_index, self.error_mask, self.reg0_reads)
                return
            time.sleep(0.5)
            reg0 = self._read_register0()
            if reg0 is None:
                self.finished.emit(False, self.test_index, self.error_mask, self.reg0_reads)
                return
            self.reg0_reads.append(reg0)
            feedback_byte = self._select_feedback_byte(reg0)
            mismatch = high_byte ^ feedback_byte
            self.error_mask |= mismatch
            match = mismatch == 0
            combined_error_mask = self.error_mask << (8 * self.test_index)
            print(
                f"[TEST {self.test_index + 1}] step {step + 1}: "
                f"cmd={high_byte:08b} low={low_byte:08b} "
                f"reg0=0x{reg0:04X} feedback={feedback_byte:08b} match={match}"
            )
            print(f"[TEST {self.test_index + 1}] err = {self._format_error_mask(combined_error_mask)}")
        self.finished.emit(True, self.test_index, self.error_mask, self.reg0_reads)

    def _read_register0(self) -> int | None:
        req = struct.pack(">BBHH", self.slave_id, 3, 0, 1)
        crc = AutoConnectWorker._calc_crc(req)
        try:
            with self.lock:
                self.serial_port.write(req + crc.to_bytes(2, "little"))
                resp = self.serial_port.read(7)
        except Exception:
            return None
        if len(resp) != 7 or not self.checkcrc(resp):
            return None
        return int.from_bytes(resp[3:5], "big")

    def _select_feedback_byte(self, reg0: int) -> int:
        low_byte = reg0 & 0xFF
        high_byte = (reg0 >> 8) & 0xFF
        if high_byte and not low_byte:
            self._feedback_byte_source = "high"
        elif low_byte and not high_byte:
            self._feedback_byte_source = "low"
        if self._feedback_byte_source == "low":
            return low_byte
        return high_byte

    @staticmethod
    def _format_error_mask(mask: int) -> str:
        binary = f"{mask:016b}"
        return " ".join(binary[i : i + 4] for i in range(0, 16, 4))


class UMVH(QMainWindow):

    def on_regs_polled(self, regs: list[int]):
        self._last_regs = regs
        self._last_regs_ts = time.time()


        # Обновляем глобальную карту регистров
        device_registers.update(regs)
        # обновляем UI (пример: modbus timeout лежит в reg[2])

        new_timeout = device_registers.modbustimeout

        if (not self._spin3_inited) or (new_timeout != self._spin3_last_modbus_timeout):
            with self._block_widget_signals(self.ui.spinBox_3):
                self.ui.spinBox_3.setValue(new_timeout)
            self._spin3_last_modbus_timeout = new_timeout
            self._spin3_inited = True




    SWAP_1_2_ENABLED = True

    def __init__(self):
        super().__init__()

        self.ui = Ui_MainWindow()
        self.ui.setupUi(self)

        self._spin3_inited = False
        self._spin3_last_modbus_timeout = None

        self.test_thread = None
        self.test_worker = None
        self._serial_lock = threading.Lock()  # если нет
        self._relay_feedback_error_mask = 0
        self._relay_feedback_reads = {}
        self._tests_completed = set()
        self._current_test_index = None
        self._led_hold_timer = QTimer(self)
        self._led_hold_timer.setInterval(500)
        self._led_hold_timer.timeout.connect(self._send_all_leds)
        self._pending_led_hold_stop_button = None
        self._pending_led_hold_coil_data = None
        self._active_led_hold_stop_button = None
        self._led_hold_coil_data = None

        self.setWindowIcon(QIcon(":/icons/app"))

        # при старте показываем страницу выбора файла (bootloader UI)
        if hasattr(self.ui, "stackedWidget_3") and hasattr(self.ui, "page_11"):
            self.ui.stackedWidget_3.setCurrentWidget(self.ui.page_11)

        # --- наш новый wizard на stackedWidget_4 ---
        if hasattr(self.ui, "stackedWidget_4") and hasattr(self.ui, "page_14"):
            self.ui.stackedWidget_4.setCurrentWidget(self.ui.page_14)



        # --- фикс скругления выпадающих списков --------------------------
        for combo in self.findChildren(QComboBox):
            combo.setStyleSheet(combo.styleSheet() + "combobox-popup: 0;")

            view = combo.view()
            popup = view.window()

            popup.setWindowFlags(Qt.Popup | Qt.FramelessWindowHint | Qt.NoDropShadowWindowHint)
            popup.setAttribute(Qt.WA_TranslucentBackground)

            popup.setStyleSheet("""
                QFrame { border:none; background:transparent; border-radius:12px; }
                QListView {
                    border:1px solid #c8c8c8;
                    border-radius:12px;
                    padding:4px;
                    background:#ffffff;
                    outline:0;
                }
                QListView::item          { padding:6px 12px; border-radius:6px; }
                QListView::item:hover    { background:#f0f0f0; }
                QListView::item:selected { background:#2d97ff; color:#ffffff; }
            """)

        # --- COM / потоки -----------------------------------------------
        self.selected_port = None
        self.serial_config = {}
        self.serial_port = None
        self._serial_lock = threading.Lock()

        # автоподключение (0x41)
        self.worker_thread = None
        self.worker = None

        # обновление прошивки (0x2B + 0x2A)
        self.update_thread = None
        self.updater = None

        # обновление bootloader (только 0x2A)
        self.bl_update_thread = None
        self.bl_updater = None

        # дефолтный контент textBrowser_2 (используется для возврата UI в reset/ошибках)
        self._text_browser2_defaults = (
            self.ui.textBrowser_2.toPlainText(),
            self.ui.textBrowser_2.toHtml(),
        )

        # словари для отслеживания изменений настроек (page_4)
        self._saved_regs = {}
        self._changed_regs = {}

        # --- список COM-портов ------------------------------------------
        self.populate_com_ports()

        self._com_port_timer = QTimer(self)
        self._com_port_timer.setInterval(2000)
        self._com_port_timer.timeout.connect(self.populate_com_ports)

        if hasattr(self.ui, "comboBox_11"):
            self.ui.comboBox_11.currentTextChanged.connect(self.on_port_selected)

        # --- обычная логика приложения -----------------------------------
        try:
            self.ui.stackedWidget.setCurrentWidget(self.ui.page)
        except AttributeError:
            self.ui.stackedWidget.setCurrentIndex(0)

        self._com_port_timer.start()

        # переход в режим автоподключения
        self.ui.pushButton.clicked.connect(self.start_auto_connect)
        self.ui.pushButton_2.clicked.connect(lambda: self.switch_to(self.ui.page_3))

        btn = getattr(self.ui, "pushButton_13", None)
        if btn is not None:
            btn.clicked.connect(self.on_pushButton_13_clicked)




        # page_3
        self.ui.pushButton_3.clicked.connect(lambda: self.switch_to(self.ui.page))
        self.ui.pushButton_11.clicked.connect(self.manual_connect)

        # page_2
        self.ui.pushButton_5.clicked.connect(self.stop_auto_connect)

        # page_4 (настройки/обновления)
        self.ui.pushButton_4.clicked.connect(self.apply_settings)
        self.ui.comboBox_5.currentTextChanged.connect(self._on_setting_changed)
        self.ui.comboBox_6.currentTextChanged.connect(self._on_setting_changed)
        self.ui.comboBox_7.currentIndexChanged.connect(self._on_setting_changed)
        self.ui.comboBox_8.currentTextChanged.connect(self._on_setting_changed)
        self.ui.spinBox_2.valueChanged.connect(self._on_setting_changed)
        self.ui.spinBox_3.valueChanged.connect(self._on_setting_changed)

        self.ui.OS_update.clicked.connect(self.select_firmware_file)
        self.ui.pushButton_7.clicked.connect(self.select_bootloader_file)

        self.poller = None
        self.poll_thread = None
        # --- навигация по stackedWidget_4 ---

        # page_14 -> page_15
        if hasattr(self.ui, "pushButton_8"):
            self.ui.pushButton_8.clicked.connect(
                lambda: self.ui.stackedWidget_4.setCurrentWidget(self.ui.page_15)
            )

        # page_15 -> page_16
        if hasattr(self.ui, "pushButton_12"):
            self.ui.pushButton_12.clicked.connect(
                lambda: self.ui.stackedWidget_4.setCurrentWidget(self.ui.page_16)
            )

        # page_16 -> page_17
        if hasattr(self.ui, "pushButton_10"):
            self.ui.pushButton_10.clicked.connect(
                lambda: self.ui.stackedWidget_4.setCurrentWidget(self.ui.page_17)
            )
            self.ui.pushButton_10.clicked.connect(self._on_stop_led_hold_button_clicked)

        # page_17 -> page_14 (возврат в начало)
        if hasattr(self.ui, "pushButton_15"):
            self.ui.pushButton_15.clicked.connect(
                lambda: self.ui.stackedWidget_4.setCurrentWidget(self.ui.page_14)
            )
            self.ui.pushButton_15.clicked.connect(self._on_stop_led_hold_button_clicked)
            self.ui.pushButton_15.clicked.connect(self._show_test_results)



        reset_button = getattr(self.ui, "pushButton_22", None)
        if reset_button is not None:
            reset_button.clicked.connect(self.reset_application_state)

        if hasattr(self.ui, "pushButton_9"):
            self.ui.pushButton_9.clicked.connect(self._on_test1_clicked)

            # событие 2 с page_17
        if hasattr(self.ui, "pushButton_14"):
            self.ui.pushButton_14.clicked.connect(self._on_test2_clicked)

    def start_test_sequence(self, low_fill):
        if not self.serial_port:
            QMessageBox.warning(self, "Ошибка", "Нет соединения с портом")
            self._pending_led_hold_stop_button = None
            self._pending_led_hold_coil_data = None
            return
        self.stop_led_hold()
        self.stop_polling()
        slave_id = self.ui.spinBox2.value() if hasattr(self.ui, 'spinBox2') else self.serial_config.get('usart_id', 1)
        test_index = self._current_test_index if self._current_test_index is not None else 0
        if self.test_thread:
            self.test_worker.stop()
            self.test_thread.quit()
            self.test_thread.wait()
        self.test_thread = QThread(self)
        self.test_worker = TestLedSequenceWorker(
            self.serial_port,
            slave_id,
            low_fill,
            self._serial_lock,
            test_index,
        )
        self.test_worker.moveToThread(self.test_thread)
        self.test_thread.started.connect(self.test_worker.run)
        self.test_worker.finished.connect(self.test_thread.quit)
        self.test_worker.finished.connect(self.test_worker.deleteLater)
        self.test_worker.finished.connect(self.test_finished)
        self.test_thread.finished.connect(self.test_thread.deleteLater)
        self.test_thread.finished.connect(self._on_test_thread_finished)
        self.test_thread.start()

    def test_finished(self, success, test_index, error_mask, reg0_reads):
        status = "успешно" if success else "с ошибкой"
        print(f"Тест завершён {status}")
        combined_error_mask = error_mask << (8 * test_index)
        self._relay_feedback_error_mask |= combined_error_mask
        self._relay_feedback_reads[test_index] = reg0_reads
        self._tests_completed.add(test_index)
        print(f"Итоговый err = {self._format_error_mask(self._relay_feedback_error_mask)}")
        if self._pending_led_hold_stop_button:
            self._start_led_hold(self._pending_led_hold_stop_button, self._pending_led_hold_coil_data)
        else:
            self.start_polling()
        self._pending_led_hold_stop_button = None
        self._pending_led_hold_coil_data = None

    def _on_test_thread_finished(self):
        self.test_thread = None
        self.test_worker = None
        if self._pending_led_hold_stop_button and not self._led_hold_timer.isActive():
            self._start_led_hold(self._pending_led_hold_stop_button, self._pending_led_hold_coil_data)
            self._pending_led_hold_stop_button = None
            self._pending_led_hold_coil_data = None


    # --- заглушки для тестов (добавь сюда) ---
    def _on_test1_clicked(self):
        self._relay_feedback_error_mask = 0
        self._relay_feedback_reads = {}
        self._tests_completed.clear()
        self._current_test_index = 0
        self._pending_led_hold_stop_button = "pushButton_10"
        self._pending_led_hold_coil_data = bytes([0xFF, 0xFF])
        self.start_test_sequence(0xFF)  # Низкие биты 1

    def _on_test2_clicked(self):
        self._current_test_index = 1
        self._pending_led_hold_stop_button = "pushButton_15"
        self._pending_led_hold_coil_data = bytes([0xFF, 0x00])
        self.start_test_sequence(0x00)  # Низкие биты 0

    def _start_led_hold(self, stop_button_name, coil_data):
        if not self.serial_port:
            return
        self._active_led_hold_stop_button = stop_button_name
        self._led_hold_coil_data = coil_data
        self._send_all_leds(self._led_hold_coil_data)
        if not self._led_hold_timer.isActive():
            self._led_hold_timer.start()

    def stop_led_hold(self):
        if self._led_hold_timer.isActive():
            self._led_hold_timer.stop()
        self._active_led_hold_stop_button = None
        self._led_hold_coil_data = None

    def _on_stop_led_hold_button_clicked(self):
        sender = self.sender()
        if sender is None:
            return
        sender_name = sender.objectName()
        if self._active_led_hold_stop_button == sender_name:
            self.stop_led_hold()
            self.start_polling()

    def _show_test_results(self):
        if not self._tests_completed:
            return
        if self._relay_feedback_error_mask == 0:
            QMessageBox.information(
                self,
                "Результат теста",
                "Тест прошел успешно, полное соответствие регистра обратной связи",
            )
            return
        relays = sorted(self._get_error_relays(self._relay_feedback_error_mask))
        relays_text = ", ".join(str(relay) for relay in relays)
        QMessageBox.warning(
            self,
            "Результат теста",
            f"Внимание! выявлено несоответствие регистров обратной связи и команд (реле {relays_text})",
        )

    @staticmethod
    def _get_error_relays(error_mask: int) -> set[int]:
        relays = set()
        for test_index in range(2):
            test_mask = (error_mask >> (8 * test_index)) & 0xFF
            for bit in range(8):
                if test_mask & (1 << bit):
                    relay_number = bit + 1
                    relays.add(relay_number)
        return relays

    @staticmethod
    def _format_error_mask(mask: int) -> str:
        binary = f"{mask:016b}"
        return " ".join(binary[i : i + 4] for i in range(0, 16, 4))

    def _send_all_leds(self, coil_data=None):
        if not self.serial_port:
            return
        if coil_data is None:
            coil_data = self._led_hold_coil_data
        if coil_data is None:
            return
        slave_id = self.ui.spinBox2.value() if hasattr(self.ui, "spinBox2") else self.serial_config.get("usart_id", 1)
        req_head = struct.pack(">BBHHB", slave_id, 0x0F, 0, 16, 2)
        req = req_head + coil_data
        crc_val = AutoConnectWorker._calc_crc(req)
        req += struct.pack("<H", crc_val)
        try:
            with self._serial_lock:
                self.serial_port.reset_input_buffer()
                self.serial_port.write(req)
                resp = self.serial_port.read(8)
            if len(resp) != 8 or not TestLedSequenceWorker.checkcrc(resp):
                return
        except Exception:
            return

    def switch_to(self, page_widget):
        self.ui.stackedWidget.setCurrentWidget(page_widget)
        if page_widget is self.ui.page:
            self._com_port_timer.start()
            self.populate_com_ports()
        else:
            self._com_port_timer.stop()
        if page_widget is self.ui.page_4:
            # при открытии page_4 показываем страницу выбора файла
            self.ui.stackedWidget_2.setCurrentWidget(self.ui.page_6)

    def populate_com_ports(self):
        """Заполняем comboBox_11 списком доступных COM портов."""
        ports = serial.tools.list_ports.comports()

        # сортируем список по возрастанию индекса, чтобы последний был максимальным
        def port_index(p):
            # выдёргиваем цифры из названия, например COM9 -> 9
            nums = "".join(filter(str.isdigit, p.device))
            return int(nums) if nums else -1

        ports = sorted(ports, key=port_index)

        previous_selection = self.selected_port or self.ui.comboBox_11.currentText()

        with self._block_widget_signals(self.ui.comboBox_11):
            self.ui.comboBox_11.clear()
            for port in ports:
                # добавляем имя устройства, например 'COM3'
                self.ui.comboBox_11.addItem(port.device)

            if ports:
                available_devices = {port.device for port in ports}
                if previous_selection in available_devices:
                    self.selected_port = previous_selection
                else:
                    # выбираем порт с наибольшим индексом
                    self.selected_port = ports[-1].device
                self.ui.comboBox_11.setCurrentText(self.selected_port)
            else:
                self.selected_port = None

    def on_port_selected(self, port_name: str):
        """Слот сохранения выбранного пользователем порта."""
        self.selected_port = port_name

    def on_pushButton_13_clicked(self):
        # 1) Остановить опрос, если он идет
        if hasattr(self, "stop_polling"):
            self.stop_polling()

        # 2) Закрыть текущий COM, если открыт
        if getattr(self, "serial_port", None) is not None:
            try:
                with self._serial_lock:
                    self.serial_port.close()
            except Exception:
                pass
            self.serial_port = None

        # 3) Сбросить выбранный порт (чтобы auto-select заново сработал)
        self.selected_port = None

        # 4) Перейти на стартовую страницу (там уже есть авто-обновление списка COM)
        self.switch_to(self.ui.page)



    @contextmanager
    def _block_widget_signals(self, *widgets):
        """Временное отключение сигналов заданных виджетов."""
        states: list[bool] = []
        try:
            for widget in widgets:
                if widget is None:
                    states.append(False)
                    continue
                states.append(widget.blockSignals(True))
            yield
        finally:
            for widget, state in zip(widgets, states):
                if widget is None:
                    continue
                widget.blockSignals(state)











    def _validate_password_input(self, text: str) -> tuple[bool, int | None]:
        pwd = text.strip()
        if not pwd:
            return True, None
        try:
            value = int(pwd, 0)
        except ValueError:
            QMessageBox.warning(self, "Пароль", "Неверный формат пароля.")
            return False, None
        if not (0 <= value <= 0xFFFF):
            QMessageBox.warning(self, "Пароль", "Пароль должен быть в диапазоне 0..65535.")
            return False, None
        if value != 12593:
            QMessageBox.warning(self, "Пароль", "пароль введен неверно")
            return False, None
        return True, value

    def _send_password(self, text: str) -> bool:
        is_valid, value = self._validate_password_input(text)
        if not is_valid:
            return False
        if value is None:
            self._last_calibration_password = ""
            return True
        if not self._write_register(REG_PASSWORD, value):
            self._handle_comm_error()
            return False
        self._last_calibration_password = text.strip()
        return True





    @staticmethod
    def _to_signed_16(value: int) -> int:
        value &= 0xFFFF
        return value - 0x10000 if value & 0x8000 else value







    @staticmethod
    def _has_negative_slope(x1: int | None, y1: int | None, x2: int | None, y2: int | None) -> bool:
        if None in (x1, y1, x2, y2):
            return False
        dx = x2 - x1
        if dx == 0:
            return False
        dy = y2 - y1
        return dx * dy < 0

    @staticmethod
    def _calculate_percent_range(value: int, positive: float, negative: float) -> tuple[float, float]:
        """Возвращает диапазон значения с указанными процентами отклонения."""

        lower = float(value) * (1 - negative)
        upper = float(value) * (1 + positive)
        if lower > upper:
            lower, upper = upper, lower
        return lower, upper












    # ------------------------------------------------------------------
    def start_auto_connect(self):
        """Запуск автоподключения и переход на страницу ожидания."""

        if hasattr(self, '_text_browser2_defaults'):
            # Восстанавливаем HTML, чтобы сохранить форматирование/цвет/шрифт
            self.ui.textBrowser_2.setHtml(self._text_browser2_defaults[1])
        else:
            # Если вдруг defaults не инициализировались, пишем просто текст
            self.ui.textBrowser_2.setText("Подключите устройство к ПК и перезагрузите")

        self._set_autoconnect_defaults()  # при входе на страницу выставляем базовые параметры 115200 8N1



        self.switch_to(self.ui.page_2)
        if not self.selected_port:
            return

        # создаём рабочий поток для приёма пакета
        self.worker_thread = QThread()
        self.worker = AutoConnectWorker(self.selected_port)
        self.worker.moveToThread(self.worker_thread)
        self.worker_thread.started.connect(self.worker.run)
        self.worker.finished.connect(self._auto_connect_finished)
        self.worker.error.connect(self._auto_connect_error)
        self.worker.finished.connect(self.worker_thread.quit)
        self.worker.error.connect(self.worker_thread.quit)  # <--- Убиваем поток при ошибке!
        self.worker_thread.start()

    def _set_autoconnect_defaults(self):
        """Выставляем значения виджетов автоподключения на 115200 8N1."""
        idx_baud = self.ui.comboBox.findText("115200")
        if idx_baud != -1:
            self.ui.comboBox.setCurrentIndex(idx_baud)  # скорость 115 200 бод

        idx_bits = self.ui.comboBox_2.findText("8")
        if idx_bits != -1:
            self.ui.comboBox_2.setCurrentIndex(idx_bits)  # 8 бит данных

        self.ui.comboBox_4.setCurrentIndex(0)  # без чётности (8N1)
        self.ui.comboBox_3.setCurrentIndex(0)  # один стоп-бит

    def _auto_connect_error(self, message: str):
        # при ошибке просто выводим её в текстовое поле
        self.ui.textBrowser_2.setText(message)

    def manual_connect(self):
        """Ручное подключение с выбранными настройками."""
        if not self.selected_port:
            return

        # получаем параметры из элементов управления
        try:
            baud = int(self.ui.comboBox.currentText())
        except ValueError:
            baud = DEFAULT_BAUDRATE
        bits = int(self.ui.comboBox_2.currentText())
        parity_idx = self.ui.comboBox_4.currentIndex()
        parity_val = {0: serial.PARITY_NONE, 1: serial.PARITY_ODD, 2: serial.PARITY_EVEN}.get(parity_idx, serial.PARITY_NONE)
        stop = 2 if self.ui.comboBox_3.currentIndex() == 1 else 1
        slave = self.ui.spinBox.value()

        # создаем временное соединение и проверяем ответ
        try:
            ser = serial.Serial(
                self.selected_port,
                baudrate=baud,
                bytesize=serial.EIGHTBITS,
                parity=parity_val,
                stopbits=serial.STOPBITS_TWO if stop == 2 else serial.STOPBITS_ONE,
                timeout=1,
            )
        except serial.SerialException as exc:
            self.ui.textBrowser_2.setText(str(exc))
            return

        # формируем запрос чтения одного регистра для проверки связи
        req = struct.pack(">BBHH", slave, 3, REG_SENSOR_READ_START, 1)  # используем новый адрес регистра для проверки связи
        crc = AutoConnectWorker._calc_crc(req)
        ser.write(req + crc.to_bytes(2, "little"))
        resp = ser.read(7)

        valid = False
        if len(resp) == 7:
            recv_crc = int.from_bytes(resp[-2:], "little")
            calc_crc = AutoConnectWorker._calc_crc(resp[:-2])
            valid = recv_crc == calc_crc

        ser.close()

        if not valid:
            # если ответ не получен или CRC неверен
            self.ui.textBrowser_2.setText("\u041d\u0435\u0442 \u043e\u0442\u0432\u0435\u0442\u0430 \u043e\u0442 \u0443\u0441\u0442\u0440\u043e\u0439\u0441\u0442\u0432\u0430")
            return

        settings = {
            "baud": baud,
            "bits": bits,
            "parity": parity_idx,
            "stop": stop,
            "usart_id": slave,
        }
        # используем существующий метод для открытия порта и запуска опроса
        self._auto_connect_finished(settings)

    def _auto_connect_finished(self, settings: dict):
        """Сохранение полученных настроек и открытие порта."""
        self.serial_config = settings
        # пробуем открыть порт с полученными параметрами
        try:
            self.serial_port = serial.Serial(
                self.selected_port,
                baudrate=settings["baud"],
                bytesize=serial.EIGHTBITS,
                parity={0: serial.PARITY_NONE, 1: serial.PARITY_ODD, 2: serial.PARITY_EVEN}.get(settings["parity"], serial.PARITY_NONE),
                stopbits=serial.STOPBITS_TWO if settings["stop"] == 2 else serial.STOPBITS_ONE,
                timeout=1,
            )
        except serial.SerialException as exc:
            self.ui.textBrowser_2.setText(str(exc))
            return

        self._fill_settings_ui()
        self._capture_page4_settings()
        self.switch_to(self.ui.page_4)
        self.start_polling()

    def _fill_settings_ui(self):
        """Заполняем виджеты на page_4 полученными значениями."""
        cfg = self.serial_config
        self.ui.comboBox_5.setCurrentText(str(cfg.get("baud", "")))
        self.ui.comboBox_6.setCurrentText(str(cfg.get("bits", "")))
        parity_idx = {0: 0, 1: 1, 2: 2}.get(cfg.get("parity"), 0)
        self.ui.comboBox_7.setCurrentIndex(parity_idx)
        self.ui.comboBox_8.setCurrentText(str(cfg.get("stop", "")))
        if "usart_id" in cfg:
            self.ui.spinBox_2.setValue(cfg["usart_id"])
        self.ui.spinBox_3.setValue(device_registers.modbustimeout)


    def _capture_page4_settings(self):
        """Сохраняем текущие значения виджетов страницы."""
        self._saved_regs = self._get_current_regs()
        self._changed_regs.clear()

    def _on_setting_changed(self):
        """Обработчик изменения любых настроек на page_4."""
        current = self._get_current_regs()
        for reg, val in current.items():
            if self._saved_regs.get(reg) != val:
                self._changed_regs[reg] = val
            elif reg in self._changed_regs:
                del self._changed_regs[reg]

    def _get_current_regs(self) -> dict[int, int]:
        bits_ui = int(self.ui.comboBox_6.currentText())
        parity_ui = self.ui.comboBox_7.currentIndex()
        stop_ui = int(self.ui.comboBox_8.currentText())

        regs = {
            REG_BAUD: int(self.ui.comboBox_5.currentText()) // 100,
            REG_BITS: 0x0000 if bits_ui == 8 else 0x1000,
            REG_PARITY: {0: 0x0000, 1: 0x0600, 2: 0x0400}[parity_ui],
            REG_STOP: 0x0000 if stop_ui == 1 else 0x2000,
            REG_USART_ID: self.ui.spinBox_2.value(),
            REG_MODBUSTIMEOUT: self.ui.spinBox_3.value(),
        }
        return regs

    def _apply_new_serial(self):
        """Применяем настройки USART после отправки."""
        cfg = {
            "baud": int(self.ui.comboBox_5.currentText()),
            "bits": int(self.ui.comboBox_6.currentText()),
            "parity": self.ui.comboBox_7.currentIndex(),
            "stop": int(self.ui.comboBox_8.currentText()),
            "usart_id": self.ui.spinBox_2.value(),
        }
        try:
            if self.serial_port:
                with self._serial_lock:
                    self.serial_port.close()
            self.serial_port = serial.Serial(
                self.selected_port,
                baudrate=cfg["baud"],
                bytesize=serial.EIGHTBITS ,
                parity={0: serial.PARITY_NONE, 1: serial.PARITY_ODD, 2: serial.PARITY_EVEN}.get(cfg["parity"], serial.PARITY_NONE),
                stopbits=serial.STOPBITS_TWO if cfg["stop"] == 2 else serial.STOPBITS_ONE,
                timeout=1,
            )
        except serial.SerialException:
            self._handle_comm_error()
            return
        self.serial_config = cfg
        self._fill_settings_ui()
        self.stop_polling()
        self.start_polling()

    def stop_auto_connect(self):
        """Останавливаем поток автоподключения и возвращаемся на главную."""
        if self.worker:
            self.worker.stop()
        if self.worker_thread:
            self.worker_thread.quit()
            self.worker_thread.wait()
        self.stop_polling()
        self.switch_to(self.ui.page)

    def reset_application_state(self):
        """Возвращаем приложение в исходное состояние и освобождаем ресурсы (без калибровки/матрицы)."""

        # --- остановка воркеров/потоков ---------------------------------
        if getattr(self, "worker", None):
            self.worker.stop()
        if getattr(self, "worker_thread", None):
            self.worker_thread.quit()
            self.worker_thread.wait()
        self.worker = None
        self.worker_thread = None

        if getattr(self, "updater", None):
            self.updater.stop()
        if getattr(self, "update_thread", None):
            self.update_thread.quit()
            self.update_thread.wait()
        self.updater = None
        self.update_thread = None

        if getattr(self, "bl_updater", None):
            self.bl_updater.stop()
        if getattr(self, "bl_update_thread", None):
            self.bl_update_thread.quit()
            self.bl_update_thread.wait()
        self.bl_updater = None
        self.bl_update_thread = None

        # Poller (теперь может читать 0..8 и хранить last_regs)
        if hasattr(self, "stop_polling"):
            self.stop_polling()
        self.poller = None
        self.poll_thread = None

        # --- serial ------------------------------------------------------
        if getattr(self, "serial_port", None):
            try:
                with self._serial_lock:
                    self.serial_port.close()
            except serial.SerialException:
                pass
        self.serial_port = None
        self.serial_config = {}

        # --- состояние приложения ---------------------------------------
        self.selected_port = None
        if hasattr(self, "_saved_regs"):
            self._saved_regs.clear()
        if hasattr(self, "_changed_regs"):
            self._changed_regs.clear()

        # если в poller хранились последние 9 регистров — сбросим кеш тут
        self._last_regs = [0] * 9
        self._last_regs_ts = 0.0

        # --- UI: сообщения/поля -----------------------------------------
        # основной лог (textBrowser_2)
        default_plain, default_html = getattr(self, "_text_browser2_defaults", ("", ""))
        if hasattr(self.ui, "textBrowser_2"):
            if default_plain.strip():
                if default_html.strip():
                    self.ui.textBrowser_2.setHtml(default_html)
                else:
                    self.ui.textBrowser_2.setPlainText(default_plain)
            else:
                self.ui.textBrowser_2.clear()

        # поле ввода пароля/команд (если есть)
        edit_sp = getattr(self.ui, "textEditSP", None)
        if edit_sp is not None:
            edit_sp.clear()

        # прогресс-бары (прошивка/бутлоадер)
        pb1 = getattr(self.ui, "progressBar", None)
        if pb1 is not None:
            pb1.setValue(0)
            pb1.setFormat("%p%")

        pb2 = getattr(self.ui, "progressBar_2", None)
        if pb2 is not None:
            pb2.setValue(0)
            pb2.setFormat("%p%")

        # страницы прогресса
        if hasattr(self.ui, "stackedWidget_2") and hasattr(self.ui, "page_6"):
            self.ui.stackedWidget_2.setCurrentWidget(self.ui.page_6)
        if hasattr(self.ui, "stackedWidget_3") and hasattr(self.ui, "page_11"):
            self.ui.stackedWidget_3.setCurrentWidget(self.ui.page_11)

        # кнопка реле/матрицы больше не нужна — но если виджет существует, прячем безопасно
        btn_relays = getattr(self.ui, "pushButton_32", None)
        if btn_relays is not None:
            btn_relays.setVisible(False)

        # дефолты автоподключения (если метод оставлен)
        if hasattr(self, "_set_autoconnect_defaults"):
            self._set_autoconnect_defaults()

        # обновить список COM-портов и вернуться на главную
        if hasattr(self, "populate_com_ports"):
            self.populate_com_ports()
        if hasattr(self, "switch_to") and hasattr(self.ui, "page"):
            self.switch_to(self.ui.page)

    # --- опрос регистров ------------------------------------------------
    def start_polling(self):
        if not self.serial_port:
            return
        if self.poll_thread and self.poll_thread.isRunning():
            return
        if self.poll_thread or self.poller:
            self.stop_polling()
        self.poll_thread = QThread()
        slave = self.serial_config.get("usart_id", 1)
        self.poller = RegisterPoller(self.serial_port, slave, self._serial_lock)
        self.poller.moveToThread(self.poll_thread)
        self.poll_thread.started.connect(self.poller.run)
        self.poller.data_ready.connect(self.on_regs_polled)
        self.poller.error.connect(self.poll_error)
        self.poller.connection_lost.connect(self._handle_comm_error)
        self.poll_thread.start()

    def stop_polling(self):
        if self.poller:
            self.poller.stop()
        if self.poll_thread:
            self.poll_thread.quit()
            self.poll_thread.wait()
        self.poller = None
        self.poll_thread = None

    def poll_error(self, msg: str):
        # выводим ошибку чтения в текстовое поле на странице ожидания
        self.ui.textBrowser_2.setText(msg)





    # --- \u043e\u0431\u043d\u043e\u0432\u043b\u0435\u043d\u0438\u0435 \u041f\u041e ---------------------------------
    def select_firmware_file(self):
        filename, _ = QFileDialog.getOpenFileName(self, "Select firmware", "", "Hex files (*.hex);;All files (*)")
        if filename and self._validate_firmware_size(filename):
            self.start_firmware_update(filename)

    def start_firmware_update(self, filename: str):
        if not self.serial_port:
            return
        self.stop_polling()
        self.ui.progressBar.setValue(0)
        self.ui.progressBar.setFormat("0% \u043f\u043e\u0434\u0433\u043e\u0442\u043e\u0432\u043a\u0430 \u043a \u043e\u0431\u043d\u043e\u0432\u043b\u0435\u043d\u0438\u044e")
        self.ui.stackedWidget_2.setCurrentWidget(self.ui.page_7)

        self.update_thread = QThread()
        slave = self.serial_config.get("usart_id", self.ui.spinBox_2.value())
        # \u043f\u043e \u0442\u0440\u0435\u0431\u043e\u0432\u0430\u043d\u0438\ю
        # \u043f\u043e\u0441\u044b\u043b\u0430\u0435\u043c \u0431\u043b\u043e\u043a\u0438
        # 0x2A \u043d\u0430 USART ID = 1
        self.updater = FirmwareUpdateWorker(self.serial_port, slave, filename, self._serial_lock)
        self.updater.moveToThread(self.update_thread)
        self.update_thread.started.connect(self.updater.run)
        self.updater.progress.connect(self.update_progress)
        self.updater.finished.connect(self.update_finished)
        self.updater.finished.connect(self.update_thread.quit)
        self.update_thread.start()

    def update_progress(self, percent: int, msg: str):
        fmt = f"{percent}%" + (f" {msg}" if msg else "")
        self.ui.progressBar.setFormat(fmt)
        self.ui.progressBar.setValue(percent)

    def update_finished(self, success: bool):
        if success:
            self.ui.stackedWidget_2.setCurrentWidget(self.ui.page_9)
            QTimer.singleShot(5000, self._finish_success)
        else:
            self.ui.stackedWidget_2.setCurrentWidget(self.ui.page_8)
            QTimer.singleShot(5000, self._finish_failure)

    def _finish_success(self):
        self.ui.stackedWidget_2.setCurrentWidget(self.ui.page_6)
        self.start_polling()

    def _finish_failure(self):
        self.switch_to(self.ui.page)
        self.start_polling()

    # --- обновление из загрузчика ---------------------------------
    def select_bootloader_file(self):
        filename, _ = QFileDialog.getOpenFileName(self, "Select firmware", "", "Hex files (*.hex);;All files (*)")
        if filename and self._validate_firmware_size(filename):
            self.start_bootloader_update(filename)

    def start_bootloader_update(self, filename: str):
        if not self.selected_port:
            return
        # останавливаем возможный опрос и закрываем порт
        self.stop_polling()
        if self.serial_port:
            with self._serial_lock:
                self.serial_port.close()
            self.serial_port = None

        self.ui.progressBar_2.setValue(0)
        self.ui.progressBar_2.setFormat("0% подготовка к обновлению")
        self.ui.stackedWidget_3.setCurrentWidget(self.ui.page_10)

        self.bl_update_thread = QThread()
        self.bl_updater = BootloaderUpdateWorker(self.selected_port, filename)
        self.bl_updater.moveToThread(self.bl_update_thread)
        self.bl_update_thread.started.connect(self.bl_updater.run)
        self.bl_updater.progress.connect(self.boot_update_progress)
        self.bl_updater.finished.connect(self.boot_update_finished)
        self.bl_updater.finished.connect(self.bl_update_thread.quit)
        self.bl_update_thread.start()

    def boot_update_progress(self, percent: int, msg: str):
        fmt = f"{percent}%" + (f" {msg}" if msg else "")
        self.ui.progressBar_2.setFormat(fmt)
        self.ui.progressBar_2.setValue(percent)

    def boot_update_finished(self, success: bool):
        if success:
            self.ui.stackedWidget_3.setCurrentWidget(self.ui.page_12)
        else:
            self.ui.stackedWidget_3.setCurrentWidget(self.ui.page_13)
        QTimer.singleShot(5000, self._boot_finish_reset)

    def _boot_finish_reset(self):
        self.ui.stackedWidget_3.setCurrentWidget(self.ui.page_11)
        self.switch_to(self.ui.page)
        self.bl_updater = None
        self.bl_update_thread = None

    def _validate_firmware_size(self, filename: str) -> bool:
        try:
            file_size = os.path.getsize(filename)
        except OSError as exc:
            QMessageBox.warning(self, "Предупреждение", f"Не удалось проверить размер файла: {exc}")
            return False

        if file_size > MAX_FIRMWARE_FILE_SIZE:
            QMessageBox.warning(self, "Предупреждение", "Файл слишком большой")
            return False

        return True

    def apply_settings(self):
        """Отправляет изменённые настройки на устройство (в т.ч. только пароль)."""
        if not self.serial_port:
            return

        # 1) Берём все изменения со страницы
        regs = self._changed_regs.copy()

        # 2) Пароль добавляем всегда, даже если других изменений нет
        pwd_text = self.ui.textEditSP.toPlainText()
        is_valid_pwd, pwd_value = self._validate_password_input(pwd_text)
        if not is_valid_pwd:
            return
        if pwd_value is not None:
            regs[REG_PASSWORD] = pwd_value

        # 3) Если после всего нечего отправлять — выходим
        if not regs:
            return

        # 4) Порядок записи регистров
        order = [
            REG_BAUD, REG_BITS, REG_PARITY, REG_STOP, REG_USART_ID, REG_MODBUSTIMEOUT
        ]
        for reg in order:
            if reg in regs:
                if not self._write_register(reg, regs[reg]):
                    self._handle_comm_error()
                    return

        # 5) Пароль — в самом конце, отдельно
        if REG_PASSWORD in regs:
            if not self._write_register(REG_PASSWORD, regs[REG_PASSWORD]):
                self._handle_comm_error()
                return

        # 6) Локальное состояние
        self._saved_regs.update(regs)
        self._changed_regs.clear()
        if any(r in regs for r in (REG_BAUD, REG_BITS, REG_PARITY, REG_STOP, REG_USART_ID, REG_MODBUSTIMEOUT)):
            self._apply_new_serial()

        # 7) Сброс UI
        self.ui.textEditSP.clear()

    def _read_register(self, addr: int) -> int | None:
        """Чтение одного регистра Modbus."""
        if not self.serial_port:
            return None
        try:
            slave = self.serial_config.get("usart_id", 1)
            req = struct.pack(">BBHH", slave, 3, addr, 1)
            crc = AutoConnectWorker._calc_crc(req)
            with self._serial_lock:
                self.serial_port.write(req + crc.to_bytes(2, "little"))
                resp = self.serial_port.read(7)
            if len(resp) != 7:
                return None
            recv_crc = int.from_bytes(resp[-2:], "little")
            if recv_crc != AutoConnectWorker._calc_crc(resp[:-2]):
                return None
            return int.from_bytes(resp[3:5], "big")
        except serial.SerialException:
            return None

    def _write_register(self, addr: int, value: int) -> bool:
        """Запись одного регистра Modbus."""
        if not self.serial_port:
            return False
        try:
            slave = self.serial_config.get("usart_id", 1)
            req = struct.pack(">BBHH", slave, 6, addr, value)
            crc = AutoConnectWorker._calc_crc(req)
            with self._serial_lock:
                self.serial_port.write(req + crc.to_bytes(2, "little"))
                resp = self.serial_port.read(8)
            if len(resp) != 8:
                return False
            recv_crc = int.from_bytes(resp[-2:], "little")
            calc_crc = AutoConnectWorker._calc_crc(resp[:-2])
            return recv_crc == calc_crc
        except serial.SerialException:
            return False



    def _handle_comm_error(self):
        """Отображает страницу ошибки и возвращается на главную."""
        self.stop_polling()
        if self.update_thread:
            self.update_thread.quit()
            self.update_thread.wait()
        if self.bl_update_thread:
            self.bl_update_thread.quit()
            self.bl_update_thread.wait()
            self.bl_update_thread = None
            self.bl_updater = None
        if self.serial_port:
            with self._serial_lock:
                self.serial_port.close()
        self.switch_to(self.ui.page_5)
        QTimer.singleShot(5000, lambda: self.switch_to(self.ui.page))

    def closeEvent(self, event):
        """Гарантируем остановку потоков при закрытии окна."""
        self.stop_polling()
        if self.update_thread:
            self.update_thread.quit()
            self.update_thread.wait()
        if self.bl_update_thread:
            self.bl_update_thread.quit()
            self.bl_update_thread.wait()
            self.bl_update_thread = None
            self.bl_updater = None
        if self.serial_port:
            with self._serial_lock:
                self.serial_port.close()
        super().closeEvent(event)


def main():
    app    = QApplication(sys.argv)
    window = UMVH()
    window.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
