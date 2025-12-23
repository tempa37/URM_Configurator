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

MAX_FIRMWARE_FILE_SIZE = 24 * 1024  # 24 КБ

# --- карта регистров ---------------------------------------------------
REG_SENSOR_TYPE_BASE = 0x000A  # тип датчика для портов 1-8
REG_SENSOR_TYPE_COUNT = 8
REG_SENSOR_READ_START = 0x0012  # показания датчиков портов 1-8
REG_SENSOR_READ_COUNT = 8
REG_SENSOR_POLL_COUNT = REG_SENSOR_TYPE_COUNT + REG_SENSOR_READ_COUNT
REG_PORT_SENSOR_BIND = 0x001A  # выбор режима, порта и типа датчика
REG_CAL_POINT_X1 = 0x001B
REG_CAL_POINT_Y1 = 0x001C
REG_CAL_POINT_X2 = 0x001D
REG_CAL_POINT_Y2 = 0x001E
REG_CAL_STATUS_START = 0x001F  # битовые маски откалиброванных датчиков
REG_CAL_STATUS_COUNT = 8
REG_BAUD = 0x0027
REG_BITS = 0x0028
REG_PARITY = 0x0029
REG_STOP = 0x002A
REG_PASSWORD = 0x002B
REG_USART_ID = 0x002C

# --- особые типы датчиков -----------------------------------------------
SENSOR_TYPE_REGISTER_VOLTAGE = 0x06
SENSOR_TYPE_CANONICAL_VOLTAGE = 0x00


def normalize_sensor_type(value: int) -> int:
    """Преобразует специальный код датчика напряжения к каноническому значению."""

    if (value & 0xFF) == SENSOR_TYPE_REGISTER_VOLTAGE:
        return (value & ~0xFF) | SENSOR_TYPE_CANONICAL_VOLTAGE
    return value

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
                timeout=AUTO_CONNECT_INTERVAL,  # выставляем таймаут, равный требуемой паузе между командами
            )
        except serial.SerialException as exc:
            self.error.emit(str(exc))
            return

        try:
            ser.reset_input_buffer()  # очищаем входной буфер перед началом обмена
        except serial.SerialException:
            pass

        while self._running:
            loop_started = time.monotonic()  # фиксируем время, чтобы выдержать паузу 200 мс
            try:
                ser.write(AUTO_CONNECT_CMD)  # отправляем команду 0x41 на устройство
            except serial.SerialException as exc:
                self.error.emit(str(exc))
                break

            data = ser.read(AUTO_CONNECT_RESPONSE_LEN)  # ждём ответ с настройками
            if len(data) >= AUTO_CONNECT_RESPONSE_LEN and self._check_crc(data):
                settings = self._parse_regs(data)
                ser.close()  # сразу закрываем порт, чтобы освободить ресурс перед выходом из потока
                self.finished.emit(settings)
                return

            remaining = AUTO_CONNECT_INTERVAL - (time.monotonic() - loop_started)
            if remaining > 0:
                time.sleep(remaining)  # дожидаемся остаток периода, чтобы выдержать тайминг 200 мс

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
        """Возвращает настройки, извлечённые из пакета."""
        # данные начинаются после трёх байт заголовка
        regs = [int.from_bytes(packet[3 + i * 2 : 5 + i * 2], byteorder="big") for i in range(6)]
        return {
            "baud": regs[0] * 100,
            "bits" : regs[1],
            "parity": regs[2],
            "stop": regs[3],
            "usart_id": regs[4],
        }


class RegisterPoller(QObject):
    """Поток опроса регистров устройства."""

    data_ready = Signal(list, list, list)
    error = Signal(str)
    connection_lost = Signal()

    def __init__(self, serial_port: serial.Serial, slave_id: int, lock: threading.Lock):
        super().__init__()
        self.serial_port = serial_port
        self.slave_id = slave_id
        self._lock = lock
        self._running = True
        self._fail_count = 0

    def stop(self):
        self._running = False

    def run(self):
        while self._running:
            try:
                sensor_regs = self._read_registers(REG_SENSOR_TYPE_BASE, REG_SENSOR_POLL_COUNT)
                if sensor_regs is None:
                    continue
                raw_sensor_types = sensor_regs[:REG_SENSOR_TYPE_COUNT]
                sensor_types = [normalize_sensor_type(value) for value in raw_sensor_types]
                sensor_values = sensor_regs[REG_SENSOR_TYPE_COUNT:]

                status_regs = self._read_registers(REG_CAL_STATUS_START, REG_CAL_STATUS_COUNT)
                if status_regs is None:
                    continue

                self._fail_count = 0
                self.data_ready.emit(sensor_types, sensor_values, status_regs)
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

    def __init__(self, serial_port: serial.Serial, slave_id: int, filename: str):
        super().__init__()
        self.serial_port = serial_port
        self.slave_id = slave_id
        self.filename = filename
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

        for _ in range(MAX_RETRIES):
            try:
                self.serial_port.write(frame)
                resp = self.serial_port.read(8)
                if len(resp) >= 4:
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
                timeout=1,
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

        for _ in range(MAX_RETRIES):
            try:
                ser.write(frame)
                resp = ser.read(8)
                if len(resp) >= 4:
                    return True
            except serial.SerialException:
                pass
            time.sleep(RETRY_DELAY)
        return False

class UMVH(QMainWindow):


    SWAP_1_2_ENABLED = True


    def __init__(self):
        super().__init__()
        self.ui = Ui_MainWindow()
        self.ui.setupUi(self)

        self.setWindowIcon(QIcon(":/icons/app"))
        # при старте показываем страницу выбора файла
        self.ui.stackedWidget_3.setCurrentWidget(self.ui.page_11)

        # --- фикс скругления выпадающих списков --------------------------
        for combo in self.findChildren(QComboBox):
            # (опционально) делаем popup дочерним, а не отдельным окном
            combo.setStyleSheet(combo.styleSheet() + "combobox-popup: 0;")

            view   = combo.view()          # QListView
            popup  = view.window()         # QComboBoxPrivateContainer (QFrame)

            # 1) убираем системную рамку и тень
            popup.setWindowFlags(Qt.Popup |
                                 Qt.FramelessWindowHint |
                                 Qt.NoDropShadowWindowHint)

            # 2) разрешаем прозрачный фон, чтобы радиус «обрезал» углы
            popup.setAttribute(Qt.WA_TranslucentBackground)

            # 3) задаём стиль контейнеру + самому списку
            popup.setStyleSheet("""
                /* сам контейнер -----------------------------------------*/
                QFrame { border:none; background:transparent; border-radius:12px; }

                /* список внутри (можно скопировать ваш QSS) ------------*/
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

        # --- загрузка списка COM-портов ---------------------------------
        self.selected_port = None  # переменная для хранения выбранного порта
        self.serial_config = {}
        self.serial_port = None
        self._serial_lock = threading.Lock()
        self.worker_thread = None
        self.worker = None
        self.poll_thread = None
        self.poller = None
        self.update_thread = None
        self.updater = None
        self.bl_update_thread = None
        self.bl_updater = None
        self._current_calibration: str | None = None
        self._calibration_port: int | None = None
        self._calibration_sensor: int | None = None
        self._last_calibration_password: str = ""
        self._two_point_data: dict[str, int | None] = {"x1": None, "y1": None, "x2": None, "y2": None}
        self._four_point_data: dict[str, int | None] = {"x1": None, "y1": None, "x2": None, "y2": None}
        self._latest_sensor_types: list[int] = [0] * REG_SENSOR_TYPE_COUNT
        self._latest_sensor_values: list[int] = [0] * REG_SENSOR_READ_COUNT
        self._latest_calibration_masks: list[int] = [0] * REG_CAL_STATUS_COUNT
        self._relay_ports: list[int] = []  # список портов с датчиком 0x101

        if hasattr(self.ui, 'pushButton_32'):
            self.ui.pushButton_32.setVisible(False)

        self.sensor_value_widgets = [
            getattr(self.ui, f"s{row}s0x04_3") for row in range(1, REG_SENSOR_READ_COUNT + 1)
        ]
        for spinner_name in ("spinBox_11", "spinBox_12", "spinBox_3"):
            spinner = getattr(self.ui, spinner_name, None)
            if spinner is not None:
                spinner.setRange(-0x8000, 0x7FFF)
        self._calibration_matrix_cells: dict[int, dict[int, QTextBrowser]] = {}
        self._calibration_cell_defaults: dict[QTextBrowser, tuple[str, str]] = {}
        self._calibration_cell_states: dict[QTextBrowser, bool] = {}
        self._calibration_highlight_style = "background-color:rgb(140, 140, 140);"
        reference_browser = getattr(self.ui, "textBrowser_25", None)
        if reference_browser is not None and reference_browser.styleSheet():
            self._calibration_highlight_style = reference_browser.styleSheet()
        for port in range(1, REG_SENSOR_TYPE_COUNT + 1):
            cells: dict[int, QTextBrowser] = {}
            for sensor_code in (0x04, 0x02, 0x01, 0x00):
                widget = getattr(self.ui, f"s{port}s0x{sensor_code:02X}", None)
                if widget is None:
                    continue
                cells[sensor_code] = widget
                self._calibration_cell_defaults[widget] = (widget.styleSheet(), widget.toHtml())
                self._calibration_cell_states[widget] = False
            self._calibration_matrix_cells[port] = cells
        self._scale_hint_defaults: dict[QTextBrowser, tuple[str, str]] = {}
        for name in ("textBrowser_70", "textBrowser_72"):
            browser = getattr(self.ui, name, None)
            if browser is not None:
                self._scale_hint_defaults[browser] = (browser.toPlainText(), browser.toHtml())
        self._text_browser2_defaults: tuple[str, str] = (
            self.ui.textBrowser_2.toPlainText(),
            self.ui.textBrowser_2.toHtml(),
        )
        # словари для отслеживания изменений настроек
        self._saved_regs: dict[int, int] = {}
        self._changed_regs: dict[int, int] = {}
        self.populate_com_ports()

        # таймер для периодического обновления списка COM-портов на главной странице
        self._com_port_timer = QTimer(self)
        self._com_port_timer.setInterval(2000)
        self._com_port_timer.timeout.connect(self.populate_com_ports)
        # реагируем на смену выбора пользователем
        self.ui.comboBox_11.currentTextChanged.connect(self.on_port_selected)

        # --- обычная логика вашего приложения ----------------------------
        try:
            self.ui.stackedWidget.setCurrentWidget(self.ui.page)
        except AttributeError:
            self.ui.stackedWidget.setCurrentIndex(0)

        # запускаем обновление списка COM-портов, пока отображается главная страница
        self._com_port_timer.start()

        # переход в режим автоподключения
        self.ui.pushButton.clicked.connect(self.start_auto_connect)
        self.ui.pushButton_2.clicked.connect(lambda: self.switch_to(self.ui.page_3))

        # кнопка "Назад" на page_3
        self.ui.pushButton_3.clicked.connect(lambda: self.switch_to(self.ui.page))
        # кнопка "Подключиться" на page_3
        self.ui.pushButton_11.clicked.connect(self.manual_connect)
        # кнопка "Назад" на page_2
        self.ui.pushButton_5.clicked.connect(self.stop_auto_connect)

        # обработчики изменений на page_4
        self.ui.pushButton_4.clicked.connect(self.apply_settings)
        self.ui.comboBox_5.currentTextChanged.connect(self._on_setting_changed)
        self.ui.comboBox_6.currentTextChanged.connect(self._on_setting_changed)
        self.ui.comboBox_7.currentIndexChanged.connect(self._on_setting_changed)
        self.ui.comboBox_8.currentTextChanged.connect(self._on_setting_changed)
        self.ui.spinBox_2.valueChanged.connect(self._on_setting_changed)
        self.ui.OS_update.clicked.connect(self.select_firmware_file)
        self.ui.pushButton_7.clicked.connect(self.select_bootloader_file)
        reset_button = getattr(self.ui, "pushButton_22", None)
        if reset_button is not None:
            reset_button.clicked.connect(self.reset_application_state)

        # Подключаем обработчик кнопки управления реле
        if hasattr(self.ui, 'pushButton_32'):
            self.ui.pushButton_32.clicked.connect(self.toggle_relays)

        self._init_calibration_connections()

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

    def _map_port_ui_to_device(self, port: int) -> int:
        """UI→Device: при выборе порта в UI возвращаем фактический порт на устройстве."""
        if not self.SWAP_1_2_ENABLED:
            return port
        return 2 if port == 1 else 1 if port == 2 else port

    def _map_port_device_to_ui(self, port: int) -> int:
        """Device→UI: преобразуем номер порта из устройства в отображаемый в интерфейсе."""
        if not self.SWAP_1_2_ENABLED:
            return port
        return 2 if port == 1 else 1 if port == 2 else port

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

    def _swap_regs_for_ui(self, regs: list[int]) -> list[int]:
        """Device→UI: перед отображением меняем местами строки портов 1↔2."""
        if not self.SWAP_1_2_ENABLED:
            return regs
        if len(regs) >= 2:
            regs = regs.copy()
            regs[0], regs[1] = regs[1], regs[0]  # 0→порт1, 1→порт2
        return regs

    # --- калибровка ---------------------------------------------------
    def _init_calibration_connections(self):
        """Настраиваем обработчики кнопок области калибровки."""
        self.ui.pushButton_10.clicked.connect(self._start_two_point_calibration)
        self.ui.pushButton_12.clicked.connect(self._start_four_point_calibration)
        self.ui.pushButton_23.clicked.connect(self._start_clear_calibration)

        self.ui.pushButton_15.clicked.connect(self._cancel_calibration)
        self.ui.pushButton_8.clicked.connect(self._confirm_two_point_port)
        self.ui.pushButton_14.clicked.connect(self._back_to_two_point_port_selection)
        self.ui.pushButton_13.clicked.connect(self._two_point_submit_password)
        self.ui.pushButton_16.clicked.connect(self._two_point_commit_y1)
        self.ui.pushButton_19.clicked.connect(self._two_point_clear_current_calibration)
        self.ui.pushButton_20.clicked.connect(self._back_to_two_point_y1)
        self.ui.pushButton_17.clicked.connect(self._two_point_commit_y2)
        self.ui.pushButton_21.clicked.connect(self._back_to_two_point_y2)
        self.ui.pushButton_18.clicked.connect(self._two_point_finalize)

        self.ui.pushButton_25.clicked.connect(self._cancel_calibration)
        self.ui.pushButton_24.clicked.connect(self._four_point_to_values)
        self.ui.pushButton_29.clicked.connect(self._four_point_back_to_select)
        self.ui.pushButton_28.clicked.connect(self._four_point_to_password)
        self.ui.pushButton_31.clicked.connect(self._four_point_back_to_values)
        self.ui.pushButton_30.clicked.connect(self._four_point_finalize)

        self.ui.pushButton_26.clicked.connect(self._cancel_calibration)
        self.ui.pushButton_27.clicked.connect(self._clear_calibration_execute)

        self._reset_calibration_state()

    def _reset_calibration_state(self):
        """Возвращаем зону калибровки в исходное состояние."""
        self._current_calibration = None
        self._calibration_port = None
        self._calibration_sensor = None
        for data in (self._two_point_data, self._four_point_data):
            data.update({"x1": None, "y1": None, "x2": None, "y2": None})

        self.ui.comboBox_9.setCurrentIndex(0)
        self.ui.comboBox_10.setCurrentIndex(0)
        self.ui.comboBox_12.setCurrentIndex(0)
        self.ui.comboBox_13.setCurrentIndex(0)
        self.ui.comboBox_14.setCurrentIndex(0)

        for editor in (self.ui.textEditSP_2, self.ui.textEditSP_3, self.ui.textEditSP_4, self.ui.textEditSP_5):
            editor.clear()

        for spinner in (
            self.ui.spinBox_10,
            self.ui.spinBox_11,
            self.ui.spinBox_12,
            self.ui.spinBox_13,
            self.ui.spinBox_3,
            self.ui.spinBox_20,
            self.ui.spinBox_18,
            self.ui.spinBox_19,
            self.ui.spinBox_17,
        ):
            spinner.setValue(0)

        self._set_calibration_page(self.ui.page_16)
        self._update_calibration_headers()

    def _set_calibration_page(self, page: QWidget):
        self.ui.stackedWidget_4.setCurrentWidget(page)
        if page is getattr(self.ui, "page_15", None):
            self._apply_scale_hint(getattr(self.ui, "textBrowser_70", None))
        elif page is getattr(self.ui, "page_18", None):
            self._apply_scale_hint(getattr(self.ui, "textBrowser_72", None))
        if page is getattr(self.ui, "page_20", None):
            self._update_four_point_labels_for_sensor()
        self._update_four_point_value_edit_state()

    def _update_text_browser(self, browser: QTextBrowser | None, value: str):
        if browser is None:
            return
        browser.setPlainText(value)

    def _update_four_point_labels_for_sensor(self):
        """Обновляем подписи точек для четырёхточечной калибровки."""

        defaults = {
            "textBrowser_100": "точка x1",
            "textBrowser_97": "точка x2",
            "textBrowser_99": "точка y1",
            "textBrowser_98": "точка y2",
        }
        namur_overrides = {
            "textBrowser_100": "Обрыв",
            "textBrowser_97": "Норма (+20/-50%)",
            "textBrowser_99": "Сработал (+20/-15%)",
            "textBrowser_98": "КЗ (+5/-10%)",
        }

        sensor_code = (self._calibration_sensor & 0xFF) if self._calibration_sensor is not None else None
        labels = namur_overrides if sensor_code == 0x01 else defaults

        for name, default_text in defaults.items():
            text = labels.get(name, default_text)
            browser = getattr(self.ui, name, None)
            self._update_text_browser(browser, text)

    def _apply_scale_hint(self, browser: QTextBrowser | None):
        if browser is None:
            return
        defaults = self._scale_hint_defaults.get(browser)
        if defaults is None:
            defaults = (browser.toPlainText(), browser.toHtml())
            self._scale_hint_defaults[browser] = defaults
        base_plain, base_html = defaults
        suffix = self._sensor_scale_suffix(self._calibration_sensor)
        if suffix:
            new_plain = f"{base_plain} /{suffix}"
        else:
            new_plain = base_plain
        if base_plain in base_html:
            browser.setHtml(base_html.replace(base_plain, new_plain, 1))
        else:
            browser.setPlainText(new_plain)

    @staticmethod
    def _sensor_scale_suffix(sensor: int | None) -> str:
        if sensor is None:
            return ""
        code = sensor & 0xFF
        if code in (SENSOR_TYPE_CANONICAL_VOLTAGE, 0x04, 0x06):
            return "100"
        if code == 0x02:
            return "10"
        return ""

    def _format_sensor_type(self, sensor_code: int | None) -> str:
        if sensor_code is None:
            return "—"
        for combo in (self.ui.comboBox_12, self.ui.comboBox_14):
            for idx in range(combo.count()):
                text = combo.itemText(idx)
                try:
                    code = int(text.split()[0], 16) & 0xFF
                except ValueError:
                    continue
                if code == sensor_code:
                    return text
        return f"0x{sensor_code & 0xFF:02X}"

    def _update_calibration_headers(self):
        text = self._format_sensor_type(self._calibration_sensor)
        port_text = str(self._calibration_port) if self._calibration_port else "—"

        self._update_text_browser(getattr(self.ui, "textBrowser_113", None), text)
        self._update_text_browser(getattr(self.ui, "textBrowser_114", None), port_text)
        self._update_text_browser(getattr(self.ui, "textBrowser_69", None), text)
        self._update_text_browser(getattr(self.ui, "textBrowser_89", None), port_text)
        self._update_text_browser(getattr(self.ui, "textBrowser_81", None), text)
        self._update_text_browser(getattr(self.ui, "textBrowser_87", None), port_text)
        self._update_text_browser(getattr(self.ui, "textBrowser_90", None), text)
        self._update_text_browser(getattr(self.ui, "textBrowser_93", None), port_text)

        self._update_text_browser(getattr(self.ui, "textBrowser_105", None), port_text)
        self._update_text_browser(getattr(self.ui, "textBrowser_107", None), text)
        self._update_four_point_value_edit_state()

    def _update_four_point_value_edit_state(self):
        spin_x1 = getattr(self.ui, "spinBox_20", None)
        spin_x2 = getattr(self.ui, "spinBox_18", None)
        if not all((spin_x1, spin_x2)):
            return

        for widget in (spin_x1, spin_x2):
            widget.setEnabled(True)

    def _write_calibration_register(self, mode: int, port: int, sensor: int) -> bool:
        port_device = self._map_port_ui_to_device(port)
        value = ((mode & 0x1) << 15) | ((port_device & 0xF) << 4) | (sensor & 0xF)
        if not self._write_register(REG_PORT_SENSOR_BIND, value):
            self._handle_comm_error()
            return False
        return True

    @staticmethod
    def _trim_sensor_code(text: str) -> str:
        token = text.strip()
        if not token:
            return ""
        allowed = set("0123456789abcdefABCDEFxX")
        result_chars: list[str] = []
        for ch in token:
            if ch not in allowed:
                break
            result_chars.append(ch)
            if len(result_chars) >= 4:
                break
        return "".join(result_chars)

    def _remember_calibration_target(self, mode: int, port: int, sensor: int) -> bool:
        """Записываем выбор порта/датчика и сохраняем его в состоянии."""
        sensor_canonical = normalize_sensor_type(sensor)
        if not self._write_calibration_register(mode, port, sensor_canonical):
            return False
        self._calibration_port = port
        self._calibration_sensor = sensor_canonical
        self._update_calibration_headers()
        return True

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
        if value != 30105:
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

    def _get_sensor_type_from_device(self, port: int) -> int | None:
        address = REG_SENSOR_TYPE_BASE + (port - 1)
        value = self._read_register(address)
        if value is None:
            self._handle_comm_error()
        return value

    def _get_latest_sensor_value(self, port: int | None) -> int:
        if not port:
            return 0
        idx = port - 1
        if 0 <= idx < len(self._latest_sensor_values):
            return self._latest_sensor_values[idx]
        return 0

    @staticmethod
    def _to_signed_16(value: int) -> int:
        value &= 0xFFFF
        return value - 0x10000 if value & 0x8000 else value

    @staticmethod
    def _apply_sensor_scaling(value: int, sensor_type: int) -> float | int:
        code = sensor_type & 0xFF
        if code in (SENSOR_TYPE_CANONICAL_VOLTAGE, 0x04, 0x06):
            return value / 100
        if code == 0x02:
            return value / 10
        return value

    @staticmethod
    def _format_namur_value(value: int) -> str:
        state = (value >> 12) & 0xF
        if state == 0x3:
            frequency = value & 0x0FFF
            return str(frequency)
        return f"0x{state:02X}"

    def _format_scaled_sensor_value(self, value: int, sensor: int | None) -> str | None:
        if sensor is None:
            return None
        code = sensor & 0xFF
        if code in (SENSOR_TYPE_CANONICAL_VOLTAGE, 0x04, 0x06):
            return f"{value / 100:.2f}"
        if code == 0x02:
            return f"{value / 10:.1f}"
        return None

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

    def _namur_calibration_ranges_intersect(self, values: dict[int, int]) -> bool:
        """Проверяем, что диапазоны NAMUR не пересекаются друг с другом."""

        sensor_code = (self._calibration_sensor & 0xFF) if self._calibration_sensor is not None else None
        if sensor_code != 0x01:
            return False

        ranges = []
        ranges.append(self._calculate_percent_range(values.get(REG_CAL_POINT_X1, 0), 0.0, 0.0))
        ranges.append(self._calculate_percent_range(values.get(REG_CAL_POINT_X2, 0), 0.20, 0.50))
        ranges.append(self._calculate_percent_range(values.get(REG_CAL_POINT_Y1, 0), 0.20, 0.15))
        ranges.append(self._calculate_percent_range(values.get(REG_CAL_POINT_Y2, 0), 0.05, 0.10))

        for idx, current in enumerate(ranges):
            for other in ranges[:idx]:
                if current[0] <= other[1] and other[0] <= current[1]:
                    return True
        return False

    def _update_live_sensor_widgets(self):
        port = self._calibration_port
        if not port:
            return
        value = self._get_latest_sensor_value(port)
        for widget in (self.ui.spinBox_11, self.ui.spinBox_12):
            if widget is None:
                continue
            block = widget.blockSignals(True)
            widget.setValue(value)
            widget.blockSignals(block)

        data = self._two_point_data
        if all(data.get(key) is not None for key in ("x1", "y1", "x2", "y2")):
            x1, y1 = data["x1"], data["y1"]
            x2, y2 = data["x2"], data["y2"]
            if x1 == x2:
                result = y1
            else:
                result = y1 + (value - x1) * (y2 - y1) / (x2 - x1)
            result = int(round(result))
            result = max(-0x8000, min(result, 0x7FFF))
            block = self.ui.spinBox_3.blockSignals(True)
            self.ui.spinBox_3.setValue(result)
            formatted = self._format_scaled_sensor_value(result, self._calibration_sensor)
            if formatted is not None:
                editor = self.ui.spinBox_3.lineEdit()
                if editor is not None:
                    editor.setText(formatted)
            self.ui.spinBox_3.blockSignals(block)

    def _start_two_point_calibration(self):
        self._reset_calibration_state()
        self._current_calibration = "2pt"
        self._set_calibration_page(self.ui.page_17)

    def _confirm_two_point_port(self):
        text = self.ui.comboBox_9.currentText().strip()
        if not text.isdigit():
            QMessageBox.warning(self, "Калибровка", "Выберите номер порта.")
            return
        port = int(text)
        sensor = self._get_sensor_type_from_device(port)
        if sensor is None:
            return
        sensor_code = sensor & 0xFF
        if sensor_code == SENSOR_TYPE_CANONICAL_VOLTAGE:
            QMessageBox.warning(self, "Калибровка", "В порту отсутствует датчик")
            return
        allowed_sensor_codes = {0x01, 0x02, 0x04, SENSOR_TYPE_REGISTER_VOLTAGE}
        if sensor_code not in allowed_sensor_codes:
            QMessageBox.warning(
                self,
                "Калибровка",
                "в порту стоит датчик который нельзя откалибровать",
            )
            return
        if sensor_code == 0x01:
            QMessageBox.warning(
                self,
                "Калибровка",
                "NAMUR можно откалибровать только по 4м точкам",
            )
            return
        if sensor_code == SENSOR_TYPE_REGISTER_VOLTAGE:
            sensor = normalize_sensor_type(sensor)
        if not self._remember_calibration_target(0, port, sensor):
            return
        self._set_calibration_page(self.ui.page_14)

    def _back_to_two_point_port_selection(self):
        if self._calibration_port and self._calibration_sensor is not None:
            for reg in (
                REG_CAL_POINT_X1,
                REG_CAL_POINT_X2,
                REG_CAL_POINT_Y1,
                REG_CAL_POINT_Y2,
            ):
                if not self._write_register(reg, 0):
                    self._handle_comm_error()
                    break
            self._write_calibration_register(0, self._calibration_port, self._calibration_sensor)
            self._two_point_data.update({"x1": None, "y1": None, "x2": None, "y2": None})
        self._set_calibration_page(self.ui.page_17)

    def _two_point_submit_password(self):
        if not self._calibration_port:
            return
        if self._calibration_sensor is None:
            return
        port = self._calibration_port
        sensor = self._calibration_sensor

        if not self._write_calibration_register(1, port, sensor):
            return

        defaults = (
            (REG_CAL_POINT_X1, 10),
            (REG_CAL_POINT_Y1, 10),
            (REG_CAL_POINT_X2, 100),
            (REG_CAL_POINT_Y2, 100),
        )

        for reg, value in defaults:
            if not self._write_register(reg, value):
                self._handle_comm_error()
                self._write_calibration_register(0, port, sensor)
                return

        if not self._send_password(self.ui.textEditSP_2.toPlainText()):
            self._write_calibration_register(0, port, sensor)
            return
        self.ui.textEditSP_2.clear()
        self._two_point_data.update({"x1": 10, "y1": 10, "x2": 100, "y2": 100})

        if not self._write_calibration_register(0, port, sensor):
            return
        self._set_calibration_page(self.ui.page_15)
        self._update_live_sensor_widgets()

    def _two_point_clear_current_calibration(self):
        if not self._calibration_port or self._calibration_sensor is None:
            self._reset_calibration_state()
            return

        port = self._calibration_port
        sensor = self._calibration_sensor

        if not self._write_calibration_register(1, port, sensor):
            return

        for reg in (REG_CAL_POINT_X1, REG_CAL_POINT_X2, REG_CAL_POINT_Y1, REG_CAL_POINT_Y2):
            if not self._write_register(reg, 0):
                self._handle_comm_error()
                self._write_calibration_register(0, port, sensor)
                return

        password_text = self.ui.textEditSP_3.toPlainText()
        if not password_text.strip():
            password_text = self._last_calibration_password

        if not self._send_password(password_text):
            self._write_calibration_register(0, port, sensor)
            return

        if not self._write_calibration_register(0, port, sensor):
            return

        self._two_point_data.update({"x1": 0, "y1": 0, "x2": 0, "y2": 0})
        self._reset_calibration_state()

    def _two_point_commit_y1(self):
        if not self._calibration_port:
            return
        y1 = self.ui.spinBox_10.value()
        if not self._write_register(REG_CAL_POINT_Y1, y1):
            self._handle_comm_error()
            return
        self._two_point_data["y1"] = y1
        self._two_point_data["x1"] = self.ui.spinBox_11.value()
        self._set_calibration_page(self.ui.page_18)
        self._update_live_sensor_widgets()

    def _back_to_two_point_y1(self):
        self._set_calibration_page(self.ui.page_15)

    def _two_point_commit_y2(self):
        if not self._calibration_port:
            return
        y2 = self.ui.spinBox_13.value()
        if not self._write_register(REG_CAL_POINT_Y2, y2):
            self._handle_comm_error()
            return
        self._two_point_data["y2"] = y2
        self._two_point_data["x2"] = self.ui.spinBox_12.value()
        self._set_calibration_page(self.ui.page_19)
        self._update_live_sensor_widgets()

    def _back_to_two_point_y2(self):
        self._set_calibration_page(self.ui.page_18)

    def _two_point_finalize(self):
        if not self._calibration_port:
            return
        y1 = self._two_point_data.get("y1")
        if y1 is None:
            y1 = self.ui.spinBox_10.value()
            self._two_point_data["y1"] = y1
        y2 = self._two_point_data.get("y2")
        if y2 is None:
            y2 = self.ui.spinBox_13.value()
            self._two_point_data["y2"] = y2
        x1 = self._read_register(REG_CAL_POINT_X1)
        x2 = self._read_register(REG_CAL_POINT_X2)
        if x1 is None:
            x1 = self._two_point_data.get("x1")
        if x2 is None:
            x2 = self._two_point_data.get("x2")
        if self._has_negative_slope(x1, y1, x2, y2):
            QMessageBox.warning(self, "Калибровка", "точки образуют отрицательный наклон")
            return
        # при необходимости повторно записываем точки
        for key, reg in (("y1", REG_CAL_POINT_Y1), ("y2", REG_CAL_POINT_Y2)):
            value = self._two_point_data.get(key)
            if value is None:
                value = self.ui.spinBox_13.value() if key == "y2" else self.ui.spinBox_10.value()
                if not self._write_register(reg, value):
                    self._handle_comm_error()
                    return
        if not self._send_password(self.ui.textEditSP_3.toPlainText()):
            return
        self._reset_calibration_state()

    def _start_four_point_calibration(self):
        self._reset_calibration_state()
        self._current_calibration = "4pt"
        self._set_calibration_page(self.ui.page_22)

    def _four_point_to_values(self):
        port_text = self.ui.comboBox_10.currentText().strip()
        if not port_text.isdigit():
            QMessageBox.warning(self, "Калибровка", "Выберите номер порта.")
            return
        sensor_text = self.ui.comboBox_12.currentText().strip()
        sensor_code_text = self._trim_sensor_code(sensor_text)
        if not sensor_code_text:
            QMessageBox.warning(self, "Калибровка", "Выберите тип датчика.")
            return
        try:
            sensor_code = int(sensor_code_text, 16)
        except ValueError:
            QMessageBox.warning(self, "Калибровка", "Выберите тип датчика.")
            return
        port = int(port_text)
        if not self._remember_calibration_target(1, port, sensor_code):
            return
        self._set_calibration_page(self.ui.page_20)

    def _four_point_back_to_select(self):
        self._set_calibration_page(self.ui.page_22)

    def _four_point_to_password(self):
        if not self._calibration_port:
            return
        values = {
            REG_CAL_POINT_X1: self.ui.spinBox_20.value(),
            REG_CAL_POINT_X2: self.ui.spinBox_18.value(),
            REG_CAL_POINT_Y1: self.ui.spinBox_19.value(),
            REG_CAL_POINT_Y2: self.ui.spinBox_17.value(),
        }
        if self._namur_calibration_ranges_intersect(values):
            QMessageBox.warning(self, "Калибровка", "Диапазоны точек пересекаются")
            return
        for reg, value in values.items():
            if not self._write_register(reg, value):
                self._handle_comm_error()
                return
        self._four_point_data["x1"] = values[REG_CAL_POINT_X1]
        self._four_point_data["x2"] = values[REG_CAL_POINT_X2]
        self._four_point_data["y1"] = values[REG_CAL_POINT_Y1]
        self._four_point_data["y2"] = values[REG_CAL_POINT_Y2]
        self._set_calibration_page(self.ui.page_21)

    def _four_point_back_to_values(self):
        self._set_calibration_page(self.ui.page_20)

    def _four_point_finalize(self):
        if not self._calibration_port:
            return
        data = self._four_point_data
        values = {
            REG_CAL_POINT_X1: data.get("x1", self.ui.spinBox_20.value()),
            REG_CAL_POINT_X2: data.get("x2", self.ui.spinBox_18.value()),
            REG_CAL_POINT_Y1: data.get("y1", self.ui.spinBox_19.value()),
            REG_CAL_POINT_Y2: data.get("y2", self.ui.spinBox_17.value()),
        }
        if self._has_negative_slope(
            values.get(REG_CAL_POINT_X1),
            values.get(REG_CAL_POINT_Y1),
            values.get(REG_CAL_POINT_X2),
            values.get(REG_CAL_POINT_Y2),
        ):
            QMessageBox.warning(self, "Калибровка", "точки образуют отрицательный наклон")
            return
        for reg, value in values.items():
            if not self._write_register(reg, value):
                self._handle_comm_error()
                return
        if not self._send_password(self.ui.textEditSP_4.toPlainText()):
            return
        self._reset_calibration_state()

    def _start_clear_calibration(self):
        self._reset_calibration_state()
        self._current_calibration = "clear"
        self._set_calibration_page(self.ui.page_23)

    def _clear_calibration_execute(self):
        port_text = self.ui.comboBox_13.currentText().strip()
        if not port_text.isdigit():
            QMessageBox.warning(self, "Калибровка", "Выберите номер порта.")
            return
        sensor_text = self.ui.comboBox_14.currentText().strip()
        sensor_code_text = self._trim_sensor_code(sensor_text)
        if not sensor_code_text:
            QMessageBox.warning(self, "Калибровка", "Выберите тип датчика.")
            return
        try:
            sensor_code = int(sensor_code_text, 16)
        except ValueError:
            QMessageBox.warning(self, "Калибровка", "Выберите тип датчика.")
            return
        port = int(port_text)
        if not self._write_calibration_register(1, port, sensor_code):
            return
        for reg in (REG_CAL_POINT_X1, REG_CAL_POINT_X2, REG_CAL_POINT_Y1, REG_CAL_POINT_Y2):
            if not self._write_register(reg, 0):
                self._handle_comm_error()
                return
        if not self._send_password(self.ui.textEditSP_5.toPlainText()):
            return
        # возвращаемся в режим без калибровки
        self._write_calibration_register(0, port, sensor_code)
        self._reset_calibration_state()

    def _cancel_calibration(self):
        self._reset_calibration_state()

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
        self._reset_calibration_state()
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
        """Возвращает словарь регистр -> значение из UI."""
        regs = {
            REG_BAUD: int(self.ui.comboBox_5.currentText()) // 100,
            REG_BITS: int(self.ui.comboBox_6.currentText()),
            REG_PARITY: self.ui.comboBox_7.currentIndex(),
            REG_STOP: int(self.ui.comboBox_8.currentText()),
            REG_USART_ID: self.ui.spinBox_2.value(),
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
        """Возвращаем приложение в исходное состояние и освобождаем ресурсы."""
        if self.worker:
            self.worker.stop()
        if self.worker_thread:
            self.worker_thread.quit()
            self.worker_thread.wait()
        self.worker = None
        self.worker_thread = None

        if self.updater:
            self.updater.stop()
        if self.update_thread:
            self.update_thread.quit()
            self.update_thread.wait()
        self.updater = None
        self.update_thread = None

        if self.bl_updater:
            self.bl_updater.stop()
        if self.bl_update_thread:
            self.bl_update_thread.quit()
            self.bl_update_thread.wait()
        self.bl_updater = None
        self.bl_update_thread = None

        self.stop_polling()
        self.poller = None
        self.poll_thread = None

        if self.serial_port:
            try:
                self.serial_port.close()
            except serial.SerialException:
                pass
        self.serial_port = None
        self.serial_config = {}

        self.selected_port = None
        self._saved_regs.clear()
        self._changed_regs.clear()

        self._current_calibration = None
        self._calibration_port = None
        self._calibration_sensor = None
        self._two_point_data = {"x1": None, "y1": None, "x2": None, "y2": None}
        self._four_point_data = {"x1": None, "y1": None, "x2": None, "y2": None}
        self._latest_sensor_types = [0] * REG_SENSOR_TYPE_COUNT
        self._latest_sensor_values = [0] * REG_SENSOR_READ_COUNT
        self._latest_calibration_masks = [0] * REG_CAL_STATUS_COUNT

        for widget in self.sensor_value_widgets:
            if widget is not None:
                widget.clear()

        self._reset_calibration_state()

        for widget, (style, html) in self._calibration_cell_defaults.items():
            if widget is None:
                continue
            widget.setStyleSheet(style)
            if html:
                widget.setHtml(html)
            else:
                widget.clear()
            self._calibration_cell_states[widget] = False

        self.ui.textEditSP.clear()
        default_plain, default_html = getattr(self, "_text_browser2_defaults", ("", ""))
        if default_plain.strip():
            if default_html.strip():
                self.ui.textBrowser_2.setHtml(default_html)
            else:
                self.ui.textBrowser_2.setPlainText(default_plain)
        else:
            self.ui.textBrowser_2.clear()
        for name in ("textEditSP_2", "textEditSP_3", "textEditSP_4", "textEditSP_5"):
            editor = getattr(self.ui, name, None)
            if editor is not None:
                editor.clear()

        if hasattr(self.ui, "progressBar"):
            self.ui.progressBar.setValue(0)
            self.ui.progressBar.setFormat("%p%")
        if hasattr(self.ui, "progressBar_2"):
            self.ui.progressBar_2.setValue(0)
            self.ui.progressBar_2.setFormat("%p%")

        if hasattr(self.ui, "stackedWidget_2") and hasattr(self.ui, "page_6"):
            self.ui.stackedWidget_2.setCurrentWidget(self.ui.page_6)
        if hasattr(self.ui, "stackedWidget_3") and hasattr(self.ui, "page_11"):
            self.ui.stackedWidget_3.setCurrentWidget(self.ui.page_11)

        self._latest_calibration_masks = [0] * REG_CAL_STATUS_COUNT
        self._relay_ports = []
        if hasattr(self.ui, 'pushButton_32'):
            self.ui.pushButton_32.setVisible(False)
        self._set_autoconnect_defaults()
        self.populate_com_ports()
        self.switch_to(self.ui.page)

    # --- опрос регистров ------------------------------------------------
    def start_polling(self):
        if not self.serial_port:
            return
        self.poll_thread = QThread()
        slave = self.serial_config.get("usart_id", 1)
        self.poller = RegisterPoller(self.serial_port, slave, self._serial_lock)
        self.poller.moveToThread(self.poll_thread)
        self.poll_thread.started.connect(self.poller.run)
        self.poller.data_ready.connect(self.update_sensor_table)
        self.poller.error.connect(self.poll_error)
        self.poller.connection_lost.connect(self._handle_comm_error)
        self.poll_thread.start()

    def stop_polling(self):
        if self.poller:
            self.poller.stop()
        if self.poll_thread:
            self.poll_thread.quit()
            self.poll_thread.wait()

    def poll_error(self, msg: str):
        # выводим ошибку чтения в текстовое поле на странице ожидания
        self.ui.textBrowser_2.setText(msg)

    def update_sensor_table(self, sensor_types: list[int], regs: list[int], calibration_masks: list[int]):
        """Обновляем показания датчиков и связанные элементы UI."""
        # типы датчиков привязаны к тем же индексам, что и регистры 0x0012..0x0019,
        # поэтому оставляем их без перестановки, а маски калибровки продолжаем
        # отображать в порядке UI
        sensor_types_ui = [normalize_sensor_type(value) for value in sensor_types]
        calibration_masks = self._swap_regs_for_ui(calibration_masks)
        self._latest_sensor_types = sensor_types_ui
        # показания датчиков строго соответствуют порядку регистров 0x0012..0x0019,
        # поэтому не меняем их местами даже при активном SWAP_1_2_ENABLED
        self._latest_calibration_masks = calibration_masks[:]

        converted_values: list[int] = []
        for idx, raw_value in enumerate(regs):
            sensor_type = sensor_types_ui[idx] if idx < len(sensor_types_ui) else 0
            sensor_code = sensor_type & 0xFF
            value = self._to_signed_16(raw_value) if sensor_code == 0x02 else raw_value
            converted_values.append(value)

            widget = self.sensor_value_widgets[idx] if idx < len(self.sensor_value_widgets) else None
            if widget is None:
                continue
            if sensor_code == 0x01:
                widget.setPlainText(self._format_namur_value(raw_value))
                continue
            scaled_value = self._apply_sensor_scaling(value, sensor_type)
            widget.setPlainText(str(scaled_value))

        # показания датчиков строго соответствуют порядку регистров 0x0012..0x0019,
        # поэтому не меняем их местами даже при активном SWAP_1_2_ENABLED
        self._latest_sensor_values = converted_values

        self._check_relay_sensors(sensor_types_ui)

        self._update_live_sensor_widgets()
        self._update_calibration_matrix(calibration_masks)

    def _check_relay_sensors(self, sensor_types: list[int]):
        """Проверяет наличие датчиков реле 0x101 и управляет видимостью кнопки."""
        if not hasattr(self.ui, 'pushButton_32'):
            return

        # Находим все порты с датчиком 0x101
        relay_ports = []
        for port_index, sensor_type in enumerate(sensor_types, start=1):
            if sensor_type == 0x05:
                relay_ports.append(port_index)

        # Сохраняем список портов с реле
        self._relay_ports = relay_ports

        # Показываем кнопку только если есть хотя бы одно реле
        self.ui.pushButton_32.setVisible(len(relay_ports) > 0)

    def toggle_relays(self):
        """Переключает состояние всех реле (датчик 0x101)."""
        if not self._relay_ports:
            return

        if not self.serial_port:
            self._handle_comm_error()
            return

        # Проходим по всем портам с реле
        for port in self._relay_ports:
            # Индекс в массиве показаний (port - 1)
            value_index = port - 1

            # Получаем текущее состояние из последних показаний
            if value_index >= len(self._latest_sensor_values):
                continue

            current_state = self._latest_sensor_values[value_index]

            # Новое состояние: если 0, то 1; иначе 0
            new_state = 0x0001 if current_state == 0 else 0x0000

            # Адрес регистра состояния для этого порта
            reg_address = REG_SENSOR_READ_START + (port - 1)

            # Отправляем команду 0x05 (Write Single Coil)
            if not self._write_coil(reg_address, new_state):
                self._handle_comm_error()
                return

    def _update_calibration_matrix(self, masks: list[int]):
        for port_index, mask in enumerate(masks, start=1):
            cells = self._calibration_matrix_cells.get(port_index, {})
            for sensor_code, widget in cells.items():
                if widget is None:
                    continue
                bit_index = sensor_code & 0x0F
                highlighted = bool(mask & (1 << bit_index))
                previous = self._calibration_cell_states.get(widget)
                if previous is not None and highlighted == previous:
                    continue
                default_style, default_html = self._calibration_cell_defaults.get(widget, ("", ""))
                if highlighted:
                    widget.setStyleSheet(self._calibration_highlight_style)
                    widget.setHtml("<p align=\"center\">Задано</p>")
                else:
                    widget.setStyleSheet(default_style)
                    if default_html:
                        widget.setHtml(default_html)
                    else:
                        widget.clear()
                self._calibration_cell_states[widget] = highlighted

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
        self.updater = FirmwareUpdateWorker(self.serial_port, slave, filename)
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
            REG_BAUD, REG_BITS, REG_PARITY, REG_STOP, REG_USART_ID,
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
        if any(r in regs for r in (REG_BAUD, REG_BITS, REG_PARITY, REG_STOP, REG_USART_ID)):
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

    def _write_coil(self, addr: int, value: int) -> bool:
            """Запись одного coil Modbus функцией 0x05."""
            if not self.serial_port:
                return False
            try:
                slave = self.serial_config.get('usart_id', 1)
                # Функция 0x05, значение 0xFF00 для ON или 0x0000 для OFF
                coil_value = 0xFF00 if value else 0x0000
                req = struct.pack('>BBHH', slave, 5, addr, coil_value)
                crc = AutoConnectWorker._calc_crc(req)
                with self._serial_lock:
                    self.serial_port.write(req + crc.to_bytes(2, 'little'))
                    resp = self.serial_port.read(8)
                if len(resp) != 8:
                    return False
                recv_crc = int.from_bytes(resp[-2:], 'little')
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
            self.serial_port.close()
        super().closeEvent(event)


def main():
    app    = QApplication(sys.argv)
    window = UMVH()
    window.show()
    sys.exit(app.exec())


if __name__ == "__main__":
    main()
