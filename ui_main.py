# -*- coding: utf-8 -*-

################################################################################
## Form generated from reading UI file 'untitled_old.ui'
##
## Created by: Qt User Interface Compiler version 6.9.1
##
## WARNING! All changes made in this file will be lost when recompiling UI file!
################################################################################

from PySide6.QtCore import (QCoreApplication, QDate, QDateTime, QLocale,
    QMetaObject, QObject, QPoint, QRect,
    QSize, QTime, QUrl, Qt)
from PySide6.QtGui import (QBrush, QColor, QConicalGradient, QCursor,
    QFont, QFontDatabase, QGradient, QIcon,
    QImage, QKeySequence, QLinearGradient, QPainter,
    QPalette, QPixmap, QRadialGradient, QTransform)
from PySide6.QtWidgets import (QApplication, QComboBox, QFrame, QGridLayout,
    QHBoxLayout, QMainWindow, QProgressBar, QPushButton,
    QSizePolicy, QSpacerItem, QSpinBox, QSplitter,
    QStackedWidget, QTextBrowser, QTextEdit, QVBoxLayout,
    QWidget)
import myicon

class Ui_MainWindow(object):
    def setupUi(self, MainWindow):
        if not MainWindow.objectName():
            MainWindow.setObjectName(u"MainWindow")
        MainWindow.resize(1058, 862)
        MainWindow.setMinimumSize(QSize(1058, 859))
        MainWindow.setLayoutDirection(Qt.LayoutDirection.RightToLeft)
        MainWindow.setStyleSheet(u"background-color: rgb(89, 89, 89);\n"
"\n"
"font-family: Noto Sans SC")
        self.centralwidget = QWidget(MainWindow)
        self.centralwidget.setObjectName(u"centralwidget")
        self.centralwidget.setMinimumSize(QSize(850, 820))
        self.centralwidget.setLayoutDirection(Qt.LayoutDirection.RightToLeft)
        self.centralwidget.setStyleSheet(u"QComboBox {\n"
"    combobox-popup: 0;        /* \u0437\u0430\u043f\u0440\u0435\u0442 \u043e\u0442\u0434\u0435\u043b\u044c\u043d\u043e\u0433\u043e \u043e\u043a\u043d\u0430-popup */\n"
"}")
        self.horizontalLayout_2 = QHBoxLayout(self.centralwidget)
        self.horizontalLayout_2.setObjectName(u"horizontalLayout_2")
        self.frame = QFrame(self.centralwidget)
        self.frame.setObjectName(u"frame")
        self.frame.setMinimumSize(QSize(900, 820))
        self.frame.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame.setFrameShadow(QFrame.Shadow.Raised)
        self.gridLayout_4 = QGridLayout(self.frame)
        self.gridLayout_4.setObjectName(u"gridLayout_4")
        self.verticalSpacer_2 = QSpacerItem(20, 40, QSizePolicy.Policy.Minimum, QSizePolicy.Policy.Expanding)

        self.gridLayout_4.addItem(self.verticalSpacer_2, 1, 1, 1, 1)

        self.stackedWidget = QStackedWidget(self.frame)
        self.stackedWidget.setObjectName(u"stackedWidget")
        self.stackedWidget.setMinimumSize(QSize(600, 60))
        self.stackedWidget.setLayoutDirection(Qt.LayoutDirection.RightToLeft)
        self.page = QWidget()
        self.page.setObjectName(u"page")
        self.page.setMinimumSize(QSize(900, 0))
        self.page.setStyleSheet(u"/* ===== QComboBox: \u043f\u043e\u043b\u043d\u044b\u0439 \u0441\u0442\u0438\u043b\u044c \u0431\u0435\u0437 \u0440\u0435\u0441\u0443\u0440\u0441\u043e\u0432 ===== */\n"
"QFrame#qt_combo_box_popup {\n"
"    background: transparent;   /* \u2190 \u0444\u043e\u043d \u043f\u043e\u043b\u043d\u043e\u0441\u0442\u044c\u044e \u201c\u0434\u044b\u0440\u044f\u0432\u044b\u0439\u201d */\n"
"    border: none;\n"
"    border-radius: 12px;\n"
"}\n"
"\n"
"\n"
"/* \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 \u0432\u0435\u0440\u0442\u0438\u043a\u0430\u043b\u044c\u043d\u044b\u0439 \u0441\u043a\u0440\u043e\u043b\u043b\u0431\u0430\u0440 \u0432\u043d\u0443\u0442\u0440\u0438 \u0432\u044b\u043f\u0430\u0434\u0430\u044e\u0449\u0435\u0433\u043e \u0441\u043f\u0438\u0441\u043a\u0430 \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 */\n"
"QComboBox QAbstractItemView QScrollBar:vertical {\n"
"    width: 12px;               /* \u0442\u043e\u043b\u0449\u0438\u043d\u0430 \u0432\u0441\u0435\u0439 \u043f\u043e\u043b\u043e"
                        "\u0441\u044b \u043f\u0440\u043e\u043a\u0440\u0443\u0442\u043a\u0438          */\n"
"    margin: 0px 0px 0px 0;     /* \u043b\u0451\u0433\u043a\u0438\u0439 \u043e\u0442\u0441\u0442\u0443\u043f \u043e\u0442 \u043f\u0440\u0430\u0432\u043e\u0439 \u0433\u0440\u0430\u043d\u0438 \u0441\u043f\u0438\u0441\u043a\u0430   */\n"
"    background: #ffffff;   /* \u2190 \u0443\u0431\u0438\u0440\u0430\u0435\u043c \u0444\u043e\u043d \u0441\u0430\u043c\u043e\u0439 \u043f\u043e\u043b\u043e\u0441\u044b             */\n"
"    border: none;              /* \u0438 \u0440\u0430\u043c\u043a\u0443, \u043a\u043e\u0442\u043e\u0440\u0443\u044e Qt \u0440\u0438\u0441\u0443\u0435\u0442 \u043f\u043e \u0443\u043c\u043e\u043b\u0447\u0430\u043d\u0438\u044e*/\n"
"}\n"
"\n"
"/* track (\u043a\u043e\u043b\u0435\u044f). \u0414\u0435\u043b\u0430\u0435\u043c \u0435\u0451 \u043d\u0435\u0432\u0438\u0434\u0438\u043c\u043e\u0439 \u2014 \u043e\u0441\u0442\u0430\u0451\u0442\u0441\u044f \u00ab\u043f\u0443\u0441\u0442\u043e\u0435 \u043c\u0435\u0441\u0442\u043e\u00bb"
                        " */\n"
"QComboBox QAbstractItemView QScrollBar::groove:vertical {\n"
"    background: #ffffff;   /* \u043d\u0438\u043a\u0430\u043a\u043e\u0433\u043e \u0446\u0432\u0435\u0442\u0430                         */\n"
"    border: none;\n"
"    margin: 0;                 /* \u0432\u0430\u0436\u043d\u043e! \u0443\u0431\u0438\u0440\u0430\u0435\u0442 \u0432\u043d\u0443\u0442\u0440\u0435\u043d\u043d\u0438\u0435 \u00ab\u043f\u043e\u043b\u044f\u00bb Qt    */\n"
"}\n"
"\n"
"/* \u043f\u0443\u0441\u0442\u044b\u0435 \u0443\u0447\u0430\u0441\u0442\u043a\u0438 \u043d\u0430\u0434 \u0438 \u043f\u043e\u0434 \u043f\u043e\u043b\u0437\u0443\u043d\u043a\u043e\u043c \u2014 \u0442\u043e\u0436\u0435 \u0432 \u043d\u043e\u043b\u044c */\n"
"QComboBox QAbstractItemView QScrollBar::add-page:vertical,\n"
"QComboBox QAbstractItemView QScrollBar::sub-page:vertical {\n"
"    background: #ffffff;\n"
"    border: none;\n"
"}\n"
"\n"
"/* \u0441\u0430\u043c \u043f\u043e\u043b\u0437\u0443\u043d\u043e\u043a (\u00ab\u043e\u0432\u0430\u043b\u00bb) --------"
                        "-----------------------------------------*/\n"
"QComboBox QAbstractItemView QScrollBar::handle:vertical {\n"
"    background: #808080;       /* \u0446\u0432\u0435\u0442 \u00ab\u0442\u0430\u0431\u043b\u0435\u0442\u043a\u0438\u00bb                        */\n"
"    border-radius: 999px;        /* \u0441\u043a\u0440\u0443\u0433\u043b\u044f\u0435\u043c \u043a\u0440\u0430\u044f \u043f\u043e \u043f\u043e\u043b\u043d\u043e\u0439               */\n"
"    min-height: 24px;          /* \u0447\u0442\u043e\u0431\u044b \u043d\u0435 \u0438\u0441\u0447\u0435\u0437\u0430\u043b \u043f\u0440\u0438 \u043c\u0430\u043b\u0435\u043d\u044c\u043a\u043e\u043c \u043a\u043e\u043d\u0442\u0435\u043d\u0442\u0435*/\n"
"    margin: 2px;               /* \u0437\u0430\u0437\u043e\u0440 \u043e\u0442 \u0433\u0440\u0430\u043d\u0438\u0446 \u0431\u0430\u0440\u0430                   */\n"
"}\n"
"\n"
"QComboBox QAbstractItemView QScrollBar::sub-line:vertical,   /* \u0432\u0435\u0440\u0445\u043d\u044f\u044f  */\n"
"QComboBox QAbstractItemView QScrollBa"
                        "r::add-line:vertical {  /* \u043d\u0438\u0436\u043d\u044f\u044f   */\n"
"    height: 0px;                /* \u0443\u0431\u0438\u0440\u0430\u0435\u043c \u0432\u0438\u0434\u0438\u043c\u0443\u044e \u0447\u0430\u0441\u0442\u044c      */\n"
"    width:  0px;\n"
"    border: none;\n"
"    background: #ffffff;\n"
"    subcontrol-origin: margin;  /* \u0447\u0442\u043e\u0431\u044b \u043d\u0435 \u0437\u0430\u043d\u0438\u043c\u0430\u043b\u0438 \u043c\u0435\u0441\u0442\u043e    */\n"
"}\n"
"\n"
"/* \u2500\u2500 \u0435\u0441\u043b\u0438 \u0432\u0434\u0440\u0443\u0433 \u043f\u043e\u044f\u0432\u0438\u0442\u0441\u044f \u0433\u043e\u0440\u0438\u0437\u043e\u043d\u0442\u0430\u043b\u044c\u043d\u044b\u0439 \u0441\u043a\u0440\u043e\u043b\u043b\u0431\u0430\u0440 \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500*/\n"
"QComboBox QAbstractItemView QScrollBar::sub-line:horizontal, /* \u043b\u0435\u0432\u0430\u044f    */\n"
"QComboBox QAbstractItemView QScrollBa"
                        "r::add-line:horizontal { /* \u043f\u0440\u0430\u0432\u0430\u044f  */\n"
"    width:  0px;\n"
"    height: 0px;\n"
"    border: none;\n"
"    background: #ffffff;\n"
"    subcontrol-origin: margin;\n"
"}\n"
"\n"
"/* \u041e\u0421\u041d\u041e\u0412\u041d\u041e\u0415 \u041f\u041e\u041b\u0415 -----------------------------------------------------------*/\n"
"QComboBox {\n"
"    border: 1px solid #b4b4b4;\n"
"    border-radius: 12px;\n"
"    padding: 4px 40px 4px 12px;   /* \u043c\u0435\u0441\u0442\u043e \u043f\u043e\u0434 \u0441\u0442\u0440\u0435\u043b\u043a\u0443 \u0441\u043f\u0440\u0430\u0432\u0430 */\n"
"    background: #f4f4f4;\n"
"    min-height: 60px;             /* \u0447\u0442\u043e\u0431\u044b \u043d\u0435 \u0441\u043f\u043b\u044e\u0449\u0438\u0432\u0430\u043b\u0441\u044f */\n"
"combobox-popup: 0;   \n"
"}\n"
"\n"
"/* \u041a\u041d\u041e\u041f\u041a\u0410 \u0412\u042b\u041f\u0410\u0414\u0410\u041d\u0418\u042f (\u043f\u0440\u0430\u0432\u044b\u0439 \u0441\u0435\u0433\u043c\u0435\u043d\u0442) ------------------"
                        "--------------------*/\n"
"QComboBox::drop-down {\n"
"    subcontrol-origin: padding;\n"
"    subcontrol-position: top right;\n"
"    width: 32px;\n"
"    border-left: 1px solid #b4b4b4;\n"
"    border-top-right-radius: 12px;\n"
"    border-bottom-right-radius: 12px;\n"
"    background: #e2e2e2;\n"
"}\n"
"\n"
"QComboBox::drop-down { \n"
"    background: #808080;   /* \u0432\u0440\u0435\u043c\u0435\u043d\u043d\u043e! */\n"
"}\n"
"\n"
"/* \u0421\u0422\u0420\u0415\u041b\u041a\u0410 ----------------------------------------------------------------*/\n"
"QComboBox::down-arrow {\n"
"image: url(\":/icon/arrow_drop_down_24dp_E3E3E3_FILL0_wght400_GRAD0_opsz24.png\");\n"
"    width: 24px;      /* \u043f\u043e\u0434\u0433\u043e\u043d\u0438 \u043f\u043e\u0434 \u0440\u0435\u0430\u043b\u044c\u043d\u044b\u0439 \u0440\u0430\u0437\u043c\u0435\u0440 PNG */\n"
"    height: 24px;\n"
"    margin: 0 auto;   /* \u043f\u043e \u0446\u0435\u043d\u0442\u0440\u0443 \u043a\u043d\u043e\u043f\u043a\u0438 drop\u2011down */\n"
"    border: non"
                        "e;     /* \u0433\u043b\u0443\u0448\u0438\u043c \u0432\u0441\u044f\u043a\u0438\u0435 \u0441\u0442\u0430\u0440\u044b\u0435 \u0433\u0440\u0430\u043d\u0438\u0446\u044b */\n"
"}\n"
"\n"
"/* \u041f\u043e\u0432\u043e\u0440\u043e\u0442 \u043f\u0440\u0438 \u0440\u0430\u0441\u043a\u0440\u044b\u0442\u0438\u0438 --------------------------------------------------*/\n"
"QComboBox::down-arrow:on {\n"
"    transform: rotate(180deg);\n"
"}\n"
"\n"
"\n"
"\n"
"\n"
"\n"
"/* \u0425\u041e\u0412\u0415\u0420/\u0424\u041e\u041a\u0423\u0421 -------------------------------------------------------------*/\n"
"QComboBox:hover { background: #f9f9f9; }\n"
"\n"
"QComboBox:focus {\n"
"    border: 1px solid #7aa9ff;\n"
"    outline: none;\n"
"}\n"
"\n"
"/* \u0412\u042b\u041f\u0410\u0414\u0410\u042e\u0429\u0418\u0419 \u0421\u041f\u0418\u0421\u041e\u041a -----------------------------------------------------*/\n"
"QComboBox QAbstractItemView {\n"
"    /* \u0442\u043e\u0442 \u0436\u0435 \u0440\u0430\u0434\u0438\u0443\u0441, \u0447\u0442\u043e \u0443"
                        " \u043f\u043e\u043b\u044f */\n"
"    border: 1px solid #c8c8c8;\n"
"    border-radius: 12px;\n"
"    padding: 4px;                       /* \u043b\u0451\u0433\u043a\u0438\u0439 \u00ab\u043e\u0442\u0441\u0442\u0443\u043f-\u0440\u0430\u043c\u043a\u0430\u00bb \u0432\u043d\u0443\u0442\u0440\u0438 */\n"
"    background: #FFFFFF;\n"
"\n"
"    /* \u043e\u0442\u043a\u043b\u044e\u0447\u0430\u0435\u043c \u0441\u0442\u0430\u043d\u0434\u0430\u0440\u0442\u043d\u044b\u0439 dotted focus-rectangle */\n"
"    outline: 0;                         /* Qt >5.12 \u043f\u043e\u043d\u0438\u043c\u0430\u0435\u0442 outline */\n"
"    /* \u0435\u0441\u043b\u0438 outline \u043d\u0435 \u0440\u0430\u0431\u043e\u0442\u0430\u0435\u0442 \u0432 \u0432\u0430\u0448\u0435\u0439 \u0432\u0435\u0440\u0441\u0438\u0438:\n"
"       border: none; */\n"
"}\n"
"\n"
"\n"
"QComboBox QAbstractItemView::viewport {\n"
"    border-radius: 8px;\n"
"    background: transparent;\n"
"}\n"
"\n"
"/* \u0441\u0442\u0440\u043e\u043a\u0438 \u0432\u043d\u0443\u0442\u0440\u0438"
                        " \u0441\u043f\u0438\u0441\u043a\u0430 */\n"
"QComboBox QAbstractItemView::item {\n"
"    padding: 6px 12px;\n"
"    border-radius: 6px;                 /* \u043b\u0451\u0433\u043a\u043e\u0435 \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 hover/selected */\n"
"}\n"
"\n"
"/* \u043f\u043e\u0434\u0441\u0432\u0435\u0442\u043a\u0430 \u043d\u0430\u0432\u0435\u0434\u0435\u043d\u0438\u044f  */\n"
"QComboBox QAbstractItemView::item:hover {\n"
"    background: #f0f0f0;\n"
"}\n"
"\n"
"/* \u0432\u044b\u0431\u0440\u0430\u043d\u043d\u044b\u0439 \u044d\u043b\u0435\u043c\u0435\u043d\u0442 (\u0431\u0435\u0437 \u043f\u0443\u043d\u043a\u0442\u0438\u0440\u0430!) */\n"
"QComboBox QAbstractItemView::item:selected {\n"
"    background: #2d97ff;                /* \u043f\u0440\u0438\u043c\u0435\u0440 \u0430\u043a\u0442\u0438\u0432\u043d\u043e\u0433\u043e \u0446\u0432\u0435\u0442\u0430 */\n"
"    color: #ffffff;\n"
"    outline: 0;                         /* \u0441\u0442\u0440\u0430\u0445\u043e\u0432\u043a\u0430 */\n"
"  "
                        "  /* \u0438\u043b\u0438 border: none;  -> \u0435\u0441\u043b\u0438 outline \u043d\u0435 \u043f\u043e\u0434\u0434\u0435\u0440\u0436\u0438\u0432\u0430\u0435\u0442\u0441\u044f */\n"
"}\n"
"\n"
"/* \u041e\u0444\u043e\u0440\u043c\u043b\u0435\u043d\u0438\u0435 \u0442\u0435\u043a\u0441\u0442\u0430 \u0438 \u0440\u0430\u043c\u043a\u0438 \u0434\u043b\u044f QLabel \u0438 QTextBrowser */\n"
"QLabel,\n"
"QTextBrowser {\n"
"    color: white;                    /* \u0446\u0432\u0435\u0442 \u0448\u0440\u0438\u0444\u0442\u0430 */\n"
"    border-radius: 10px;             /* \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 \u0443\u0433\u043b\u043e\u0432 \u0440\u0430\u043c\u043a\u0438 */\n"
"    padding: 6px;                    /* \u0432\u043d\u0443\u0442\u0440\u0435\u043d\u043d\u0438\u0435 \u043e\u0442\u0441\u0442\u0443\u043f\u044b */\n"
"border: 2px solid #909090; \n"
"}\n"
"\n"
"\n"
"/* \u041d\u043e\u0440\u043c\u0430\u043b\u044c\u043d\u043e\u0435 \u0441\u043e\u0441\u0442\u043e\u044f\u043d\u0438\u0435 */\n"
"QPushBu"
                        "tton {\n"
"    background-color: #404040;        /* \u0437\u0430\u043b\u0438\u0432\u043a\u0430 */\n"
"    color: white;                     /* \u0446\u0432\u0435\u0442 \u0442\u0435\u043a\u0441\u0442\u0430 */\n"
"    border: 2px solid #909090;        /* \u0442\u043e\u043b\u0449\u0438\u043d\u0430 \u0438 \u0446\u0432\u0435\u0442 \u043e\u0431\u0432\u043e\u0434\u043a\u0438 */\n"
"    border-radius: 12px;              /* \u0440\u0430\u0434\u0438\u0443\u0441 \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u044f */\n"
"    padding: 6px 12px;                /* \u00ab\u0432\u043e\u0437\u0434\u0443\u0445\u00bb \u0432\u043d\u0443\u0442\u0440\u0438 */\n"
"}\n"
"\n"
"/* \u041a\u0443\u0440\u0441\u043e\u0440 \u043d\u0430\u0432\u0435\u0434\u0451\u043d */\n"
"QPushButton:hover {\n"
"    background-color: #505050;\n"
"    border-color: #707070;\n"
"}\n"
"\n"
"/* \u041a\u043d\u043e\u043f\u043a\u0430 \u043d\u0430\u0436\u0430\u0442\u0430 (\u0443\u0434\u0435\u0440\u0436\u0438\u0432\u0430\u0435\u0442\u0441\u044f) */\n"
"QPushB"
                        "utton:pressed {\n"
"    background-color: #909090;\n"
"    border-color: #909090;\n"
"}\n"
"\n"
"/* QLabel \u0438\u043b\u0438 QTextBrowser */\n"
"QLabel, QTextBrowser {\n"
"    border: 2px solid #909090;   /* \u0442\u043e\u043b\u0449\u0438\u043d\u0430 \u0438 \u0446\u0432\u0435\u0442 */\n"
"    border-radius: 10px;         /* \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 */\n"
"    padding: 6px;                /* \u0432\u043d\u0443\u0442\u0440\u0435\u043d\u043d\u0438\u0435 \u043e\u0442\u0441\u0442\u0443\u043f\u044b */\n"
"    color: white;              /* \u0446\u0432\u0435\u0442 \u0448\u0440\u0438\u0444\u0442\u0430 */\n"
"}\n"
"\n"
"/* ===== QSpinBox \u2014 \u0441\u0442\u0438\u043b\u044c \u043f\u043e\u0434 QComboBox (\u043a\u0430\u0436\u0434\u044b\u0439 \u043f\u0430\u0440\u0430\u043c\u0435\u0442\u0440 \u043f\u043e\u0434\u043f\u0438\u0441\u0430\u043d) ===== */\n"
"\n"
"/* \u041e\u0421\u041d\u041e\u0412\u041d\u041e\u0415 \u041f\u041e\u041b\u0415 ----------------------------------------------------"
                        "-----*/\n"
"QSpinBox {\n"
"    border: 1px solid #b4b4b4;                 /* \u0432\u043d\u0435\u0448\u043d\u044f\u044f \u0440\u0430\u043c\u043a\u0430 \u0432\u0438\u0434\u0436\u0435\u0442\u0430        */\n"
"    border-radius: 12px;                       /* \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 \u0432\u0441\u0435\u0445 \u0443\u0433\u043b\u043e\u0432        */\n"
"\n"
"    padding-left: 12px;                        /* \u043e\u0442\u0441\u0442\u0443\u043f \u0442\u0435\u043a\u0441\u0442\u0430 \u0441\u043b\u0435\u0432\u0430          */\n"
"    padding-right: 40px;                       /* \u0440\u0435\u0437\u0435\u0440\u0432 \u043f\u043e\u0434 \u0431\u043b\u043e\u043a \u0441\u0442\u0440\u0435\u043b\u043e\u043a      */\n"
"    background: #f4f4f4;                       /* \u0444\u043e\u043d \u043f\u043e\u043b\u044f \u0432\u0432\u043e\u0434\u0430               */\n"
"    min-height: 60px;                          /* \u043c\u0438\u043d\u0438\u043c\u0430\u043b\u044c\u043d\u0430\u044f \u0432\u044b"
                        "\u0441\u043e\u0442\u0430 \u043a\u043e\u043d\u0442\u0440\u043e\u043b\u0430  */\n"
"    color: black;                              /* \u0446\u0432\u0435\u0442 \u0432\u0432\u0435\u0434\u0451\u043d\u043d\u043e\u0433\u043e \u0442\u0435\u043a\u0441\u0442\u0430       */\n"
"\n"
"    outline: none;                             /* \u0443\u0431\u0438\u0440\u0430\u0435\u043c \u0441\u0442\u0430\u043d\u0434\u0430\u0440\u0442\u043d\u044b\u0439 \u043f\u0443\u043d\u043a\u0442\u0438p  */\n"
"}\n"
"\n"
"/* \u0411\u041b\u041e\u041a \u0421\u0422\u0420\u0415\u041b\u041e\u041a ----------------------------------------------------------*/\n"
"/* \u043e\u0431\u0449\u0438\u0435 \u043f\u0430\u0440\u0430\u043c\u0435\u0442\u0440\u044b \u0434\u043b\u044f \u043e\u0431\u0435\u0438\u0445 \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u043e\u043a \u0431\u043b\u043e\u043a\u0430 */\n"
"QSpinBox::up-button,\n"
"QSpinBox::down-button {\n"
"    subcontrol-origin: padding;                /* \u043a\u043e\u043e\u0440\u0434\u0438\u043d\u0430\u0442\u044b \u043e"
                        "\u0442 padding-box    */\n"
"    width: 32px;                               /* \u0448\u0438\u0440\u0438\u043d\u0430 \u0441\u0435\u0433\u043c\u0435\u043d\u0442\u0430 \u0441\u043e \u0441\u0442\u0440\u0435\u043b\u043a\u0430\u043c\u0438 */\n"
"    border-left: 1px solid #b4b4b4;            /* \u043b\u0438\u043d\u0438\u044f-\u0440\u0430\u0437\u0434\u0435\u043b\u0438\u0442\u0435\u043b\u044c \u0441\u043b\u0435\u0432\u0430      */\n"
"    background: #808080;                       /* \u0444\u043e\u043d \u0431\u043b\u043e\u043a\u0430 \u0441\u0442\u0440\u0435\u043b\u043e\u043a            */\n"
"}\n"
"\n"
"/* \u2193 \u043d\u0438\u0436\u043d\u044f\u044f \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u0430 \u0431\u043b\u043e\u043a\u0430 \u0441\u0442\u0440\u0435\u043b\u043e\u043a --------------------------------------*/\n"
"QSpinBox::down-button {\n"
"    subcontrol-position: bottom right;         /* \u043f\u0440\u0438\u0432\u044f\u0437\u043a\u0430 \u043a \u043f\u0440\u0430\u0432\u043e\u043c\u0443-\u043d\u0438\u0436\u043d\u0435"
                        "\u043c\u0443   */\n"
"    height: 30%;                               /* \u0437\u0430\u043d\u0438\u043c\u0430\u0435\u043c \u043e\u0441\u0442\u0430\u0432\u0448\u0438\u0435\u0441\u044f 50 %     */\n"
"    border-bottom-right-radius: 12px;          /* \u0441\u043a\u0440\u0443\u0433\u043b\u044f\u0435\u043c \u0422\u041e\u041b\u042c\u041a\u041e \u043d\u0438\u0437-\u043f\u0440\u0430\u0432.   */\n"
"}\n"
"\n"
"\n"
"/* \u2191 \u0432\u0435\u0440\u0445\u043d\u044f\u044f \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u0430 \u0431\u043b\u043e\u043a\u0430 \u0441\u0442\u0440\u0435\u043b\u043e\u043a -------------------------------------*/\n"
"QSpinBox::up-button {\n"
"    subcontrol-position: top right;            /* \u043f\u0440\u0438\u0432\u044f\u0437\u043a\u0430 \u043a \u043f\u0440\u0430\u0432\u043e\u043c\u0443-\u0432\u0435\u0440\u0445\u043d\u0435\u043c\u0443  */\n"
"    height: 30%;                               /* \u0437\u0430\u043d\u0438\u043c\u0430\u0435\u043c \u0440\u043e\u0432\u043d\u043e \u043f\u043e\u043b\u043e\u0432\u0438"
                        "\u043d\u0443 \u0432\u044b\u0441. */\n"
"    border-top-right-radius: 12px;             /* \u0441\u043a\u0440\u0443\u0433\u043b\u044f\u0435\u043c \u0422\u041e\u041b\u042c\u041a\u041e \u0432\u0435\u0440\u0445-\u043f\u0440\u0430\u0432.  */\n"
"}\n"
"\n"
"/* \u0432\u0438\u0437\u0443\u0430\u043b\u044c\u043d\u044b\u0439 \u043e\u0442\u043a\u043b\u0438\u043a \u043f\u0440\u0438 \u043d\u0430\u0436\u0430\u0442\u0438\u0438 ----------------------------------------*/\n"
"QSpinBox::up-button:pressed,\n"
"QSpinBox::down-button:pressed {\n"
"    background: #6d6d6d;                       /* \u0437\u0430\u0442\u0435\u043c\u043d\u044f\u0435\u043c \u0444\u043e\u043d \u043d\u0430 \u0432\u0440\u0435\u043c\u044f \u043a\u043b\u0438\u043a\u0430 */\n"
"}\n"
"\n"
"/* \u0421\u0422\u0420\u0415\u041b\u041a\u0418 (\u0438\u043a\u043e\u043d\u043a\u0438) ------------------------------------------------------*/\n"
"QSpinBox::up-arrow {\n"
"    image: url(\":/icon/arrow_drop_up_24dp_E3E3E3_FILL0_wght400_GRAD0_opsz24.png\"); /* PNG/SVG \u2193 */\n"
""
                        "    width: 24px; height: 24px;                 /* \u0433\u0430\u0431\u0430\u0440\u0438\u0442\u044b \u0438\u043a\u043e\u043d\u043a\u0438              */\n"
"    margin: 0 auto;                            /* \u0446\u0435\u043d\u0442\u0440\u0438\u0440\u0443\u0435\u043c \u0432 \u0431\u043b\u043e\u043a\u0435           */\n"
"	transform: rotate(180deg);\n"
"}\n"
"\n"
"QSpinBox::down-arrow {\n"
"    image: url(\":/icon/arrow_drop_down_24dp_E3E3E3_FILL0_wght400_GRAD0_opsz24.png\"); /* PNG/SVG \u2193 */\n"
"    width: 24px; height: 24px;                 /* \u0433\u0430\u0431\u0430\u0440\u0438\u0442\u044b \u0438\u043a\u043e\u043d\u043a\u0438              */\n"
"    margin: 0 auto;                            /* \u0446\u0435\u043d\u0442\u0440\u0438\u0440\u0443\u0435\u043c \u0432 \u0431\u043b\u043e\u043a\u0435           */\n"
"}\n"
"\n"
"\n"
"/* \u043e\u0442\u043a\u043b\u044e\u0447\u0430\u0435\u043c \u043a\u043d\u043e\u043f\u043a\u0438 \u0438 \u0438\u043a\u043e\u043d\u043a\u0438 \u043f\u0440\u0438 \u0434\u043e\u0441\u0442\u0438"
                        "\u0436\u0435\u043d\u0438\u0438 min/max ---------------------*/\n"
"QSpinBox::up-button:disabled,\n"
"QSpinBox::down-button:disabled {\n"
"    background: #c8c8c8;                       /* \u0442\u0443\u0441\u043a\u043b\u044b\u0439 \u0444\u043e\u043d \u2014 \u043a\u043d\u043e\u043f\u043a\u0430 \u043d\u0435\u0430\u043a\u0442\u0438\u0432 */\n"
"}\n"
"\n"
"QSpinBox::up-arrow:disabled,\n"
"QSpinBox::down-arrow:disabled {\n"
"    image: none;                               /* \u043f\u0440\u044f\u0447\u0435\u043c \u0438\u043a\u043e\u043d\u043a\u0443 \u0443 \u043d\u0435\u0430\u043a\u0442\u0438\u0432\u043d\u043e\u0439   */\n"
"}\n"
"\n"
"/* \u0425\u041e\u0412\u0415\u0420 / \u0424\u041e\u041a\u0423\u0421 ---------------------------------------------------------*/\n"
"QSpinBox:hover  { background: #f9f9f9; }       /* \u043b\u0451\u0433\u043a\u043e\u0435 \u0432\u044b\u0441\u0432\u0435\u0442\u043b\u0435\u043d\u0438\u0435 \u043f\u0440\u0438 \u0445\u043e\u0432\u0435\u0440\u0435*/\n"
"QSpinBox:focus  { border: 1px solid #7aa9f"
                        "f; } /* \u0441\u0438\u043d\u044f\u044f \u0440\u0430\u043c\u043a\u0430 \u043f\u0440\u0438 \u0444\u043e\u043a\u0443\u0441\u0435       */\n"
"\n"
"/* \u041e\u0422\u041a\u041b\u042e\u0427\u0401\u041d\u041d\u041e\u0415 \u0421\u041e\u0421\u0422\u041e\u042f\u041d\u0418\u0415 -------------------------------------------------*/\n"
"QSpinBox:disabled {\n"
"    color: #8f8f8f;                            /* \u043f\u0440\u0438\u0433\u043b\u0443\u0448\u0430\u0435\u043c \u0442\u0435\u043a\u0441\u0442             */\n"
"    background: #e0e0e0;                       /* \u0438 \u0444\u043e\u043d \u0432\u0441\u0435\u0433\u043e \u0432\u0438\u0434\u0436\u0435\u0442\u0430          */\n"
"}\n"
"\n"
"")
        self.gridLayout_9 = QGridLayout(self.page)
        self.gridLayout_9.setObjectName(u"gridLayout_9")
        self.frame_14 = QFrame(self.page)
        self.frame_14.setObjectName(u"frame_14")
        self.frame_14.setMinimumSize(QSize(0, 100))
        self.frame_14.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_14.setFrameShadow(QFrame.Shadow.Raised)

        self.gridLayout_9.addWidget(self.frame_14, 2, 0, 1, 1)

        self.verticalLayout = QVBoxLayout()
        self.verticalLayout.setObjectName(u"verticalLayout")
        self.textBrowser = QTextBrowser(self.page)
        self.textBrowser.setObjectName(u"textBrowser")
        sizePolicy = QSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Preferred)
        sizePolicy.setHorizontalStretch(0)
        sizePolicy.setVerticalStretch(0)
        sizePolicy.setHeightForWidth(self.textBrowser.sizePolicy().hasHeightForWidth())
        self.textBrowser.setSizePolicy(sizePolicy)
        self.textBrowser.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.verticalLayout.addWidget(self.textBrowser)

        self.splitter = QSplitter(self.page)
        self.splitter.setObjectName(u"splitter")
        self.splitter.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.splitter.setOrientation(Qt.Orientation.Horizontal)
        self.comboBox_11 = QComboBox(self.splitter)
        self.comboBox_11.setObjectName(u"comboBox_11")
        self.comboBox_11.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.splitter.addWidget(self.comboBox_11)
        self.pushButton_6 = QPushButton(self.splitter)
        self.pushButton_6.setObjectName(u"pushButton_6")
        self.pushButton_6.setEnabled(False)
        sizePolicy1 = QSizePolicy(QSizePolicy.Policy.Minimum, QSizePolicy.Policy.Preferred)
        sizePolicy1.setHorizontalStretch(0)
        sizePolicy1.setVerticalStretch(0)
        sizePolicy1.setHeightForWidth(self.pushButton_6.sizePolicy().hasHeightForWidth())
        self.pushButton_6.setSizePolicy(sizePolicy1)
        self.splitter.addWidget(self.pushButton_6)

        self.verticalLayout.addWidget(self.splitter)

        self.frame_6 = QFrame(self.page)
        self.frame_6.setObjectName(u"frame_6")
        self.frame_6.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_6.setFrameShadow(QFrame.Shadow.Raised)

        self.verticalLayout.addWidget(self.frame_6)

        self.frame_2 = QFrame(self.page)
        self.frame_2.setObjectName(u"frame_2")
        self.frame_2.setMinimumSize(QSize(0, 100))
        self.frame_2.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_2.setFrameShadow(QFrame.Shadow.Raised)

        self.verticalLayout.addWidget(self.frame_2)

        self.horizontalLayout = QHBoxLayout()
        self.horizontalLayout.setObjectName(u"horizontalLayout")
        self.frame_5 = QFrame(self.page)
        self.frame_5.setObjectName(u"frame_5")
        self.frame_5.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_5.setFrameShadow(QFrame.Shadow.Raised)

        self.horizontalLayout.addWidget(self.frame_5)

        self.pushButton = QPushButton(self.page)
        self.pushButton.setObjectName(u"pushButton")
        sizePolicy1.setHeightForWidth(self.pushButton.sizePolicy().hasHeightForWidth())
        self.pushButton.setSizePolicy(sizePolicy1)
        self.pushButton.setMinimumSize(QSize(0, 4))
        self.pushButton.setMaximumSize(QSize(200, 70))

        self.horizontalLayout.addWidget(self.pushButton)

        self.frame_3 = QFrame(self.page)
        self.frame_3.setObjectName(u"frame_3")
        self.frame_3.setMinimumSize(QSize(70, 100))
        self.frame_3.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_3.setFrameShadow(QFrame.Shadow.Raised)

        self.horizontalLayout.addWidget(self.frame_3)

        self.pushButton_2 = QPushButton(self.page)
        self.pushButton_2.setObjectName(u"pushButton_2")
        sizePolicy1.setHeightForWidth(self.pushButton_2.sizePolicy().hasHeightForWidth())
        self.pushButton_2.setSizePolicy(sizePolicy1)
        self.pushButton_2.setMinimumSize(QSize(0, 0))
        self.pushButton_2.setMaximumSize(QSize(200, 70))

        self.horizontalLayout.addWidget(self.pushButton_2)

        self.frame_4 = QFrame(self.page)
        self.frame_4.setObjectName(u"frame_4")
        self.frame_4.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_4.setFrameShadow(QFrame.Shadow.Raised)

        self.horizontalLayout.addWidget(self.frame_4)


        self.verticalLayout.addLayout(self.horizontalLayout)


        self.gridLayout_9.addLayout(self.verticalLayout, 0, 0, 1, 1)

        self.stackedWidget_3 = QStackedWidget(self.page)
        self.stackedWidget_3.setObjectName(u"stackedWidget_3")
        self.page_10 = QWidget()
        self.page_10.setObjectName(u"page_10")
        self.page_10.setStyleSheet(u"/* \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 \u041f\u0420\u041e\u0413\u0420\u0415\u0421\u0421-\u0411\u0410\u0420 \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 */\n"
"\n"
"/* \u00ab\u0437\u0430\u043f\u043e\u043b\u043d\u0435\u043d\u043d\u0430\u044f\u00bb \u0447\u0430\u0441\u0442\u044c (\u0433\u043e\u0440\u0438\u0437\u043e\u043d\u0442\u0430\u043b\u044c\u043d\u0430\u044f) */\n"
"QProgressBar::chunk {\n"
"    background: #2d97ff;         /* \u0432\u0430\u0448 \u0444\u0438\u0440\u043c\u0435\u043d\u043d\u044b\u0439 \u0441\u0438\u043d\u0438\u0439                 */\n"
"    border-radius: 12px;         /* \u0447\u0442\u043e\u0431\u044b \u043a\u0440\u0430\u0439 \u0437\u0430\u043f\u043e\u043b\u043d\u0435\u043d\u0438\u044f \u0442\u043e\u0436\u0435 \u0431\u044b\u043b \u043a\u0440\u0443\u0433\u043b\u044b\u043c */\n"
"	\n"
"}\n"
"\n"
"/* \u2500\u2500 QProgressBar \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500"
                        "\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500*/\n"
"QProgressBar {\n"
"    border: 2px solid #909090;   /* \u0442\u0430\u043a\u0430\u044f \u0436\u0435 \u0440\u0430\u043c\u043a\u0430, \u043a\u0430\u043a \u0432 \u0434\u0440\u0443\u0433\u0438\u0445 \u043a\u043e\u043d\u0442\u0440\u043e\u043b\u0430\u0445 */\n"
"    border-radius: 12px;\n"
"    background: #404040;         /* \u043e\u0431\u0449\u0438\u0439 \u0442\u0451\u043c\u043d\u043e-\u0441\u0435\u0440\u044b\u0439 \u0444\u043e\u043d */\n"
"    min-height: 24px;\n"
"\n"
"    text-align: center;          /* \u043f\u0440\u043e\u0446\u0435\u043d\u0442/\u0442\u0435\u043a\u0441\u0442 \u043f\u043e \u0446\u0435\u043d\u0442\u0440\u0443 */\n"
"    color: white;                /* \u0431\u0435\u043b\u044b\u0435 \u0431\u0443\u043a\u0432\u044b \u043f\u043e\u0432\u0435\u0440\u0445 \u0441\u0438\u043d\u0435\u0433\u043e */\n"
"}\n"
"")
        self.horizontalLayout_3 = QHBoxLayout(self.page_10)
        self.horizontalLayout_3.setObjectName(u"horizontalLayout_3")
        self.frame_15 = QFrame(self.page_10)
        self.frame_15.setObjectName(u"frame_15")
        self.frame_15.setMinimumSize(QSize(150, 0))
        self.frame_15.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_15.setFrameShadow(QFrame.Shadow.Raised)

        self.horizontalLayout_3.addWidget(self.frame_15)

        self.progressBar_2 = QProgressBar(self.page_10)
        self.progressBar_2.setObjectName(u"progressBar_2")
        self.progressBar_2.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.progressBar_2.setValue(24)

        self.horizontalLayout_3.addWidget(self.progressBar_2)

        self.frame_16 = QFrame(self.page_10)
        self.frame_16.setObjectName(u"frame_16")
        self.frame_16.setMinimumSize(QSize(150, 0))
        self.frame_16.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_16.setFrameShadow(QFrame.Shadow.Raised)

        self.horizontalLayout_3.addWidget(self.frame_16)

        self.stackedWidget_3.addWidget(self.page_10)
        self.page_12 = QWidget()
        self.page_12.setObjectName(u"page_12")
        self.gridLayout_11 = QGridLayout(self.page_12)
        self.gridLayout_11.setObjectName(u"gridLayout_11")
        self.frame_20 = QFrame(self.page_12)
        self.frame_20.setObjectName(u"frame_20")
        self.frame_20.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_20.setFrameShadow(QFrame.Shadow.Raised)

        self.gridLayout_11.addWidget(self.frame_20, 0, 0, 1, 1)

        self.textBrowser_10 = QTextBrowser(self.page_12)
        self.textBrowser_10.setObjectName(u"textBrowser_10")

        self.gridLayout_11.addWidget(self.textBrowser_10, 0, 1, 1, 1)

        self.frame_19 = QFrame(self.page_12)
        self.frame_19.setObjectName(u"frame_19")
        self.frame_19.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_19.setFrameShadow(QFrame.Shadow.Raised)

        self.gridLayout_11.addWidget(self.frame_19, 0, 2, 1, 1)

        self.stackedWidget_3.addWidget(self.page_12)
        self.page_13 = QWidget()
        self.page_13.setObjectName(u"page_13")
        self.gridLayout_12 = QGridLayout(self.page_13)
        self.gridLayout_12.setObjectName(u"gridLayout_12")
        self.frame_21 = QFrame(self.page_13)
        self.frame_21.setObjectName(u"frame_21")
        self.frame_21.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_21.setFrameShadow(QFrame.Shadow.Raised)

        self.gridLayout_12.addWidget(self.frame_21, 0, 0, 1, 1)

        self.textBrowser_11 = QTextBrowser(self.page_13)
        self.textBrowser_11.setObjectName(u"textBrowser_11")

        self.gridLayout_12.addWidget(self.textBrowser_11, 0, 1, 1, 1)

        self.frame_23 = QFrame(self.page_13)
        self.frame_23.setObjectName(u"frame_23")
        self.frame_23.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_23.setFrameShadow(QFrame.Shadow.Raised)

        self.gridLayout_12.addWidget(self.frame_23, 0, 2, 1, 1)

        self.stackedWidget_3.addWidget(self.page_13)
        self.page_11 = QWidget()
        self.page_11.setObjectName(u"page_11")
        self.gridLayout_3 = QGridLayout(self.page_11)
        self.gridLayout_3.setObjectName(u"gridLayout_3")
        self.frame_17 = QFrame(self.page_11)
        self.frame_17.setObjectName(u"frame_17")
        self.frame_17.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_17.setFrameShadow(QFrame.Shadow.Raised)

        self.gridLayout_3.addWidget(self.frame_17, 0, 0, 1, 1)

        self.pushButton_7 = QPushButton(self.page_11)
        self.pushButton_7.setObjectName(u"pushButton_7")
        sizePolicy1.setHeightForWidth(self.pushButton_7.sizePolicy().hasHeightForWidth())
        self.pushButton_7.setSizePolicy(sizePolicy1)
        self.pushButton_7.setMinimumSize(QSize(200, 70))
        self.pushButton_7.setMaximumSize(QSize(220, 77))

        self.gridLayout_3.addWidget(self.pushButton_7, 0, 1, 1, 1)

        self.frame_18 = QFrame(self.page_11)
        self.frame_18.setObjectName(u"frame_18")
        self.frame_18.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_18.setFrameShadow(QFrame.Shadow.Raised)

        self.gridLayout_3.addWidget(self.frame_18, 0, 2, 1, 1)

        self.stackedWidget_3.addWidget(self.page_11)

        self.gridLayout_9.addWidget(self.stackedWidget_3, 1, 0, 1, 1)

        self.stackedWidget.addWidget(self.page)
        self.page_4 = QWidget()
        self.page_4.setObjectName(u"page_4")
        self.page_4.setMinimumSize(QSize(1023, 805))
        self.page_4.setStyleSheet(u"/* ===== QComboBox: \u043f\u043e\u043b\u043d\u044b\u0439 \u0441\u0442\u0438\u043b\u044c \u0431\u0435\u0437 \u0440\u0435\u0441\u0443\u0440\u0441\u043e\u0432 ===== */\n"
"\n"
"/* --- \u043a\u043e\u043d\u0442\u0435\u0439\u043d\u0435\u0440 \u0432\u0441\u043f\u043b\u044b\u0432\u0430\u044e\u0449\u0435\u0433\u043e \u043e\u043a\u043d\u0430 (Qt-5/6) --- */\n"
"QFrame#qt_combo_box_popup {      /* << \u043a\u043b\u044e\u0447\u0435\u0432\u0430\u044f \u0441\u0442\u0440\u043e\u0447\u043a\u0430 */\n"
"    border: none;                /* \u0443\u0431\u0438\u0440\u0430\u0435\u043c \u0440\u0430\u043c\u043a\u0443 */\n"
"    background: 505050;     /* \u0438\u043b\u0438 #505050 \u043f\u043e\u0434 \u0444\u043e\u043d \u0444\u043e\u0440\u043c\u044b */\n"
"}\n"
"\n"
"\n"
"\n"
"/* \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 \u0432\u0435\u0440\u0442\u0438\u043a\u0430\u043b\u044c\u043d\u044b\u0439 \u0441\u043a\u0440\u043e\u043b\u043b\u0431\u0430\u0440 \u0432\u043d\u0443\u0442\u0440\u0438 \u0432\u044b\u043f\u0430\u0434\u0430\u044e"
                        "\u0449\u0435\u0433\u043e \u0441\u043f\u0438\u0441\u043a\u0430 \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 */\n"
"QComboBox QAbstractItemView QScrollBar:vertical {\n"
"    width: 12px;               /* \u0442\u043e\u043b\u0449\u0438\u043d\u0430 \u0432\u0441\u0435\u0439 \u043f\u043e\u043b\u043e\u0441\u044b \u043f\u0440\u043e\u043a\u0440\u0443\u0442\u043a\u0438          */\n"
"    margin: 0px 0px 0px 0;     /* \u043b\u0451\u0433\u043a\u0438\u0439 \u043e\u0442\u0441\u0442\u0443\u043f \u043e\u0442 \u043f\u0440\u0430\u0432\u043e\u0439 \u0433\u0440\u0430\u043d\u0438 \u0441\u043f\u0438\u0441\u043a\u0430   */\n"
"    background: #ffffff;   /* \u2190 \u0443\u0431\u0438\u0440\u0430\u0435\u043c \u0444\u043e\u043d \u0441\u0430\u043c\u043e\u0439 \u043f\u043e\u043b\u043e\u0441\u044b             */\n"
"    border: none;              /* \u0438 \u0440\u0430\u043c\u043a\u0443, \u043a\u043e\u0442\u043e\u0440\u0443\u044e Qt \u0440\u0438\u0441\u0443\u0435\u0442 \u043f\u043e \u0443\u043c\u043e\u043b\u0447\u0430"
                        "\u043d\u0438\u044e*/\n"
"}\n"
"\n"
"/* track (\u043a\u043e\u043b\u0435\u044f). \u0414\u0435\u043b\u0430\u0435\u043c \u0435\u0451 \u043d\u0435\u0432\u0438\u0434\u0438\u043c\u043e\u0439 \u2014 \u043e\u0441\u0442\u0430\u0451\u0442\u0441\u044f \u00ab\u043f\u0443\u0441\u0442\u043e\u0435 \u043c\u0435\u0441\u0442\u043e\u00bb */\n"
"QComboBox QAbstractItemView QScrollBar::groove:vertical {\n"
"    background: #ffffff;   /* \u043d\u0438\u043a\u0430\u043a\u043e\u0433\u043e \u0446\u0432\u0435\u0442\u0430                         */\n"
"    border: none;\n"
"    margin: 0;                 /* \u0432\u0430\u0436\u043d\u043e! \u0443\u0431\u0438\u0440\u0430\u0435\u0442 \u0432\u043d\u0443\u0442\u0440\u0435\u043d\u043d\u0438\u0435 \u00ab\u043f\u043e\u043b\u044f\u00bb Qt    */\n"
"}\n"
"\n"
"/* \u043f\u0443\u0441\u0442\u044b\u0435 \u0443\u0447\u0430\u0441\u0442\u043a\u0438 \u043d\u0430\u0434 \u0438 \u043f\u043e\u0434 \u043f\u043e\u043b\u0437\u0443\u043d\u043a\u043e\u043c \u2014 \u0442\u043e\u0436\u0435 \u0432 \u043d\u043e\u043b\u044c"
                        " */\n"
"QComboBox QAbstractItemView QScrollBar::add-page:vertical,\n"
"QComboBox QAbstractItemView QScrollBar::sub-page:vertical {\n"
"    background: #ffffff;\n"
"    border: none;\n"
"}\n"
"\n"
"/* \u0441\u0430\u043c \u043f\u043e\u043b\u0437\u0443\u043d\u043e\u043a (\u00ab\u043e\u0432\u0430\u043b\u00bb) -------------------------------------------------*/\n"
"QComboBox QAbstractItemView QScrollBar::handle:vertical {\n"
"    background: #808080;       /* \u0446\u0432\u0435\u0442 \u00ab\u0442\u0430\u0431\u043b\u0435\u0442\u043a\u0438\u00bb                        */\n"
"    border-radius: 999px;        /* \u0441\u043a\u0440\u0443\u0433\u043b\u044f\u0435\u043c \u043a\u0440\u0430\u044f \u043f\u043e \u043f\u043e\u043b\u043d\u043e\u0439               */\n"
"    min-height: 24px;          /* \u0447\u0442\u043e\u0431\u044b \u043d\u0435 \u0438\u0441\u0447\u0435\u0437\u0430\u043b \u043f\u0440\u0438 \u043c\u0430\u043b\u0435\u043d\u044c\u043a\u043e\u043c \u043a\u043e\u043d\u0442\u0435\u043d\u0442\u0435*/\n"
"    margin: 2"
                        "px;               /* \u0437\u0430\u0437\u043e\u0440 \u043e\u0442 \u0433\u0440\u0430\u043d\u0438\u0446 \u0431\u0430\u0440\u0430                   */\n"
"}\n"
"\n"
"QComboBox QAbstractItemView QScrollBar::sub-line:vertical,   /* \u0432\u0435\u0440\u0445\u043d\u044f\u044f  */\n"
"QComboBox QAbstractItemView QScrollBar::add-line:vertical {  /* \u043d\u0438\u0436\u043d\u044f\u044f   */\n"
"    height: 0px;                /* \u0443\u0431\u0438\u0440\u0430\u0435\u043c \u0432\u0438\u0434\u0438\u043c\u0443\u044e \u0447\u0430\u0441\u0442\u044c      */\n"
"    width:  0px;\n"
"    border: none;\n"
"    background: #ffffff;\n"
"    subcontrol-origin: margin;  /* \u0447\u0442\u043e\u0431\u044b \u043d\u0435 \u0437\u0430\u043d\u0438\u043c\u0430\u043b\u0438 \u043c\u0435\u0441\u0442\u043e    */\n"
"}\n"
"\n"
"/* \u2500\u2500 \u0435\u0441\u043b\u0438 \u0432\u0434\u0440\u0443\u0433 \u043f\u043e\u044f\u0432\u0438\u0442\u0441\u044f \u0433\u043e\u0440\u0438\u0437\u043e\u043d\u0442\u0430\u043b\u044c\u043d\u044b\u0439 \u0441\u043a\u0440"
                        "\u043e\u043b\u043b\u0431\u0430\u0440 \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500*/\n"
"QComboBox QAbstractItemView QScrollBar::sub-line:horizontal, /* \u043b\u0435\u0432\u0430\u044f    */\n"
"QComboBox QAbstractItemView QScrollBar::add-line:horizontal { /* \u043f\u0440\u0430\u0432\u0430\u044f  */\n"
"    width:  0px;\n"
"    height: 0px;\n"
"    border: none;\n"
"    background: #ffffff;\n"
"    subcontrol-origin: margin;\n"
"}\n"
"\n"
"QComboBox QAbstractItemView::viewport {\n"
"    border-radius: 8px;\n"
"    background: transparent;\n"
"}\n"
"\n"
"\n"
"\n"
"/* \u041e\u0421\u041d\u041e\u0412\u041d\u041e\u0415 \u041f\u041e\u041b\u0415 -----------------------------------------------------------*/\n"
"QComboBox {\n"
"    border: 1px solid #b4b4b4;\n"
"    border-radius: 12px;\n"
"    padding: 4px 40px 4px 12px;   /* \u043c\u0435\u0441\u0442\u043e \u043f\u043e\u0434 \u0441\u0442\u0440\u0435\u043b\u043a\u0443 \u0441\u043f\u0440\u0430"
                        "\u0432\u0430 */\n"
"    background: #f4f4f4;\n"
"    min-height: 30px;             /* \u0447\u0442\u043e\u0431\u044b \u043d\u0435 \u0441\u043f\u043b\u044e\u0449\u0438\u0432\u0430\u043b\u0441\u044f */\n"
"combobox-popup: 0;   \n"
"}\n"
"\n"
"/* \u041a\u041d\u041e\u041f\u041a\u0410 \u0412\u042b\u041f\u0410\u0414\u0410\u041d\u0418\u042f (\u043f\u0440\u0430\u0432\u044b\u0439 \u0441\u0435\u0433\u043c\u0435\u043d\u0442) --------------------------------------*/\n"
"QComboBox::drop-down {\n"
"    subcontrol-origin: padding;\n"
"    subcontrol-position: top right;\n"
"    width: 40px;\n"
"    border-left: 1px solid #b4b4b4;\n"
"    border-top-right-radius: 12px;\n"
"    border-bottom-right-radius: 12px;\n"
"    background: #e2e2e2;\n"
"}\n"
"\n"
"QComboBox::drop-down { \n"
"    background: #808080;   /* \u0432\u0440\u0435\u043c\u0435\u043d\u043d\u043e! */\n"
"}\n"
"\n"
"/* \u0421\u0422\u0420\u0415\u041b\u041a\u0410 ----------------------------------------------------------------*/\n"
"QComboBox::down-arrow {\n"
"image:"
                        " url(\":/icon/arrow_drop_down_24dp_E3E3E3_FILL0_wght400_GRAD0_opsz24.png\");\n"
"    width: 24px;      /* \u043f\u043e\u0434\u0433\u043e\u043d\u0438 \u043f\u043e\u0434 \u0440\u0435\u0430\u043b\u044c\u043d\u044b\u0439 \u0440\u0430\u0437\u043c\u0435\u0440 PNG */\n"
"    height: 24px;\n"
"    margin: 0 auto;   /* \u043f\u043e \u0446\u0435\u043d\u0442\u0440\u0443 \u043a\u043d\u043e\u043f\u043a\u0438 drop\u2011down */\n"
"    border: none;     /* \u0433\u043b\u0443\u0448\u0438\u043c \u0432\u0441\u044f\u043a\u0438\u0435 \u0441\u0442\u0430\u0440\u044b\u0435 \u0433\u0440\u0430\u043d\u0438\u0446\u044b */\n"
"}\n"
"\n"
"/* \u041f\u043e\u0432\u043e\u0440\u043e\u0442 \u043f\u0440\u0438 \u0440\u0430\u0441\u043a\u0440\u044b\u0442\u0438\u0438 --------------------------------------------------*/\n"
"QComboBox::down-arrow:on {\n"
"    transform: rotate(180deg);\n"
"}\n"
"\n"
"\n"
"\n"
"\n"
"\n"
"/* \u0425\u041e\u0412\u0415\u0420/\u0424\u041e\u041a\u0423\u0421 -------------------------------------------------------------*/\n"
""
                        "QComboBox:hover { background: #f9f9f9; }\n"
"\n"
"QComboBox:focus {\n"
"    border: 1px solid #7aa9ff;\n"
"    outline: none;\n"
"}\n"
"\n"
"/* \u0412\u042b\u041f\u0410\u0414\u0410\u042e\u0429\u0418\u0419 \u0421\u041f\u0418\u0421\u041e\u041a -----------------------------------------------------*/\n"
"QComboBox QAbstractItemView {\n"
"    /* \u0442\u043e\u0442 \u0436\u0435 \u0440\u0430\u0434\u0438\u0443\u0441, \u0447\u0442\u043e \u0443 \u043f\u043e\u043b\u044f */\n"
"    border: 1px solid #c8c8c8;\n"
"    border-radius: 12px;\n"
"    padding: 4px;                       /* \u043b\u0451\u0433\u043a\u0438\u0439 \u00ab\u043e\u0442\u0441\u0442\u0443\u043f-\u0440\u0430\u043c\u043a\u0430\u00bb \u0432\u043d\u0443\u0442\u0440\u0438 */\n"
"    background: #FFFFFF;\n"
"\n"
"    /* \u043e\u0442\u043a\u043b\u044e\u0447\u0430\u0435\u043c \u0441\u0442\u0430\u043d\u0434\u0430\u0440\u0442\u043d\u044b\u0439 dotted focus-rectangle */\n"
"    outline: 0;                         /* Qt >5.12 \u043f\u043e\u043d\u0438\u043c\u0430\u0435"
                        "\u0442 outline */\n"
"    /* \u0435\u0441\u043b\u0438 outline \u043d\u0435 \u0440\u0430\u0431\u043e\u0442\u0430\u0435\u0442 \u0432 \u0432\u0430\u0448\u0435\u0439 \u0432\u0435\u0440\u0441\u0438\u0438:\n"
"       border: none; */\n"
"}\n"
"\n"
"/* \u0441\u0442\u0440\u043e\u043a\u0438 \u0432\u043d\u0443\u0442\u0440\u0438 \u0441\u043f\u0438\u0441\u043a\u0430 */\n"
"QComboBox QAbstractItemView::item {\n"
"    padding: 6px 12px;\n"
"    border-radius: 6px;                 /* \u043b\u0451\u0433\u043a\u043e\u0435 \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 hover/selected */\n"
"}\n"
"\n"
"/* \u043f\u043e\u0434\u0441\u0432\u0435\u0442\u043a\u0430 \u043d\u0430\u0432\u0435\u0434\u0435\u043d\u0438\u044f  */\n"
"QComboBox QAbstractItemView::item:hover {\n"
"    background: #f0f0f0;\n"
"}\n"
"\n"
"/* \u0432\u044b\u0431\u0440\u0430\u043d\u043d\u044b\u0439 \u044d\u043b\u0435\u043c\u0435\u043d\u0442 (\u0431\u0435\u0437 \u043f\u0443\u043d\u043a\u0442\u0438\u0440\u0430!) */\n"
"QComboBox QAbstractItemView::item:"
                        "selected {\n"
"    background: #2d97ff;                /* \u043f\u0440\u0438\u043c\u0435\u0440 \u0430\u043a\u0442\u0438\u0432\u043d\u043e\u0433\u043e \u0446\u0432\u0435\u0442\u0430 */\n"
"    color: #ffffff;\n"
"    outline: 0;                         /* \u0441\u0442\u0440\u0430\u0445\u043e\u0432\u043a\u0430 */\n"
"    /* \u0438\u043b\u0438 border: none;  -> \u0435\u0441\u043b\u0438 outline \u043d\u0435 \u043f\u043e\u0434\u0434\u0435\u0440\u0436\u0438\u0432\u0430\u0435\u0442\u0441\u044f */\n"
"}\n"
"\n"
"/* \u041e\u0444\u043e\u0440\u043c\u043b\u0435\u043d\u0438\u0435 \u0442\u0435\u043a\u0441\u0442\u0430 \u0438 \u0440\u0430\u043c\u043a\u0438 \u0434\u043b\u044f QLabel \u0438 QTextBrowser */\n"
"QLabel,\n"
"QTextBrowser {\n"
"    color: white;                    /* \u0446\u0432\u0435\u0442 \u0448\u0440\u0438\u0444\u0442\u0430 */\n"
"    border-radius: 10px;             /* \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 \u0443\u0433\u043b\u043e\u0432 \u0440\u0430\u043c\u043a\u0438 */\n"
"    padding: "
                        "6px;                    /* \u0432\u043d\u0443\u0442\u0440\u0435\u043d\u043d\u0438\u0435 \u043e\u0442\u0441\u0442\u0443\u043f\u044b */\n"
"border: 2px solid #909090; \n"
"}\n"
"\n"
"\n"
"/* \u041d\u043e\u0440\u043c\u0430\u043b\u044c\u043d\u043e\u0435 \u0441\u043e\u0441\u0442\u043e\u044f\u043d\u0438\u0435 */\n"
"QPushButton {\n"
"    background-color: #404040;        /* \u0437\u0430\u043b\u0438\u0432\u043a\u0430 */\n"
"    color: white;                     /* \u0446\u0432\u0435\u0442 \u0442\u0435\u043a\u0441\u0442\u0430 */\n"
"    border: 2px solid #909090;        /* \u0442\u043e\u043b\u0449\u0438\u043d\u0430 \u0438 \u0446\u0432\u0435\u0442 \u043e\u0431\u0432\u043e\u0434\u043a\u0438 */\n"
"    border-radius: 12px;              /* \u0440\u0430\u0434\u0438\u0443\u0441 \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u044f */\n"
"    padding: 6px 12px;                /* \u00ab\u0432\u043e\u0437\u0434\u0443\u0445\u00bb \u0432\u043d\u0443\u0442\u0440\u0438 */\n"
"}\n"
"\n"
"/* \u041a\u0443\u0440\u0441\u043e\u0440"
                        " \u043d\u0430\u0432\u0435\u0434\u0451\u043d */\n"
"QPushButton:hover {\n"
"    background-color: #505050;\n"
"    border-color: #707070;\n"
"}\n"
"\n"
"/* \u041a\u043d\u043e\u043f\u043a\u0430 \u043d\u0430\u0436\u0430\u0442\u0430 (\u0443\u0434\u0435\u0440\u0436\u0438\u0432\u0430\u0435\u0442\u0441\u044f) */\n"
"QPushButton:pressed {\n"
"    background-color: #909090;\n"
"    border-color: #909090;\n"
"}\n"
"\n"
"/* QLabel \u0438\u043b\u0438 QTextBrowser */\n"
"QLabel, QTextBrowser {\n"
"    border: 2px solid #909090;   /* \u0442\u043e\u043b\u0449\u0438\u043d\u0430 \u0438 \u0446\u0432\u0435\u0442 */\n"
"    border-radius: 10px;         /* \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 */\n"
"    padding: 6px;                /* \u0432\u043d\u0443\u0442\u0440\u0435\u043d\u043d\u0438\u0435 \u043e\u0442\u0441\u0442\u0443\u043f\u044b */\n"
"    color: white;              /* \u0446\u0432\u0435\u0442 \u0448\u0440\u0438\u0444\u0442\u0430 */\n"
"}\n"
"\n"
"/* ===== QSpinBox \u2014 \u0441\u0442\u0438\u043b\u044c"
                        " \u043f\u043e\u0434 QComboBox (\u043a\u0430\u0436\u0434\u044b\u0439 \u043f\u0430\u0440\u0430\u043c\u0435\u0442\u0440 \u043f\u043e\u0434\u043f\u0438\u0441\u0430\u043d) ===== */\n"
"\n"
"/* \u041e\u0421\u041d\u041e\u0412\u041d\u041e\u0415 \u041f\u041e\u041b\u0415 ---------------------------------------------------------*/\n"
"QSpinBox {\n"
"    border: 1px solid #b4b4b4;                 /* \u0432\u043d\u0435\u0448\u043d\u044f\u044f \u0440\u0430\u043c\u043a\u0430 \u0432\u0438\u0434\u0436\u0435\u0442\u0430        */\n"
"    border-radius: 12px;                       /* \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 \u0432\u0441\u0435\u0445 \u0443\u0433\u043b\u043e\u0432        */\n"
"\n"
"    padding-left: 12px;                        /* \u043e\u0442\u0441\u0442\u0443\u043f \u0442\u0435\u043a\u0441\u0442\u0430 \u0441\u043b\u0435\u0432\u0430          */\n"
"    padding-right: 40px;                       /* \u0440\u0435\u0437\u0435\u0440\u0432 \u043f\u043e\u0434 \u0431\u043b\u043e\u043a \u0441\u0442\u0440"
                        "\u0435\u043b\u043e\u043a      */\n"
"    background: #f4f4f4;                       /* \u0444\u043e\u043d \u043f\u043e\u043b\u044f \u0432\u0432\u043e\u0434\u0430               */\n"
"    min-height: 40px;                          /* \u043c\u0438\u043d\u0438\u043c\u0430\u043b\u044c\u043d\u0430\u044f \u0432\u044b\u0441\u043e\u0442\u0430 \u043a\u043e\u043d\u0442\u0440\u043e\u043b\u0430  */\n"
"    color: black;                              /* \u0446\u0432\u0435\u0442 \u0432\u0432\u0435\u0434\u0451\u043d\u043d\u043e\u0433\u043e \u0442\u0435\u043a\u0441\u0442\u0430       */\n"
"\n"
"    outline: none;                             /* \u0443\u0431\u0438\u0440\u0430\u0435\u043c \u0441\u0442\u0430\u043d\u0434\u0430\u0440\u0442\u043d\u044b\u0439 \u043f\u0443\u043d\u043a\u0442\u0438p  */\n"
"}\n"
"\n"
"/* \u0411\u041b\u041e\u041a \u0421\u0422\u0420\u0415\u041b\u041e\u041a ----------------------------------------------------------*/\n"
"/* \u043e\u0431\u0449\u0438\u0435 \u043f\u0430\u0440\u0430\u043c\u0435\u0442\u0440\u044b"
                        " \u0434\u043b\u044f \u043e\u0431\u0435\u0438\u0445 \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u043e\u043a \u0431\u043b\u043e\u043a\u0430 */\n"
"QSpinBox::up-button,\n"
"QSpinBox::down-button {\n"
"    subcontrol-origin: padding;                /* \u043a\u043e\u043e\u0440\u0434\u0438\u043d\u0430\u0442\u044b \u043e\u0442 padding-box    */\n"
"    width: 30px;                               /* \u0448\u0438\u0440\u0438\u043d\u0430 \u0441\u0435\u0433\u043c\u0435\u043d\u0442\u0430 \u0441\u043e \u0441\u0442\u0440\u0435\u043b\u043a\u0430\u043c\u0438 */\n"
"    border-left: 1px solid #b4b4b4;            /* \u043b\u0438\u043d\u0438\u044f-\u0440\u0430\u0437\u0434\u0435\u043b\u0438\u0442\u0435\u043b\u044c \u0441\u043b\u0435\u0432\u0430      */\n"
"    background: #808080;                       /* \u0444\u043e\u043d \u0431\u043b\u043e\u043a\u0430 \u0441\u0442\u0440\u0435\u043b\u043e\u043a            */\n"
"}\n"
"\n"
"/* \u2193 \u043d\u0438\u0436\u043d\u044f\u044f \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u0430 \u0431\u043b"
                        "\u043e\u043a\u0430 \u0441\u0442\u0440\u0435\u043b\u043e\u043a --------------------------------------*/\n"
"QSpinBox::down-button {\n"
"    subcontrol-position: bottom right;         /* \u043f\u0440\u0438\u0432\u044f\u0437\u043a\u0430 \u043a \u043f\u0440\u0430\u0432\u043e\u043c\u0443-\u043d\u0438\u0436\u043d\u0435\u043c\u0443   */\n"
"    height: 20%;                               /* \u0437\u0430\u043d\u0438\u043c\u0430\u0435\u043c \u043e\u0441\u0442\u0430\u0432\u0448\u0438\u0435\u0441\u044f 50 %     */\n"
"    border-bottom-right-radius: 12px;          /* \u0441\u043a\u0440\u0443\u0433\u043b\u044f\u0435\u043c \u0422\u041e\u041b\u042c\u041a\u041e \u043d\u0438\u0437-\u043f\u0440\u0430\u0432.   */\n"
"}\n"
"\n"
"\n"
"/* \u2191 \u0432\u0435\u0440\u0445\u043d\u044f\u044f \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u0430 \u0431\u043b\u043e\u043a\u0430 \u0441\u0442\u0440\u0435\u043b\u043e\u043a -------------------------------------*/\n"
"QSpinBox::up-button {\n"
"    subcontrol-position: top right;            /* \u043f"
                        "\u0440\u0438\u0432\u044f\u0437\u043a\u0430 \u043a \u043f\u0440\u0430\u0432\u043e\u043c\u0443-\u0432\u0435\u0440\u0445\u043d\u0435\u043c\u0443  */\n"
"    height: 20%;                               /* \u0437\u0430\u043d\u0438\u043c\u0430\u0435\u043c \u0440\u043e\u0432\u043d\u043e \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u0443 \u0432\u044b\u0441. */\n"
"    border-top-right-radius: 12px;             /* \u0441\u043a\u0440\u0443\u0433\u043b\u044f\u0435\u043c \u0422\u041e\u041b\u042c\u041a\u041e \u0432\u0435\u0440\u0445-\u043f\u0440\u0430\u0432.  */\n"
"}\n"
"\n"
"/* \u0432\u0438\u0437\u0443\u0430\u043b\u044c\u043d\u044b\u0439 \u043e\u0442\u043a\u043b\u0438\u043a \u043f\u0440\u0438 \u043d\u0430\u0436\u0430\u0442\u0438\u0438 ----------------------------------------*/\n"
"QSpinBox::up-button:pressed,\n"
"QSpinBox::down-button:pressed {\n"
"    background: #6d6d6d;                       /* \u0437\u0430\u0442\u0435\u043c\u043d\u044f\u0435\u043c \u0444\u043e\u043d \u043d\u0430 \u0432\u0440\u0435\u043c\u044f \u043a\u043b"
                        "\u0438\u043a\u0430 */\n"
"}\n"
"\n"
"/* \u0421\u0422\u0420\u0415\u041b\u041a\u0418 (\u0438\u043a\u043e\u043d\u043a\u0438) ------------------------------------------------------*/\n"
"QSpinBox::up-arrow {\n"
"    image: url(\":/icon/arrow_drop_up_24dp_E3E3E3_FILL0_wght400_GRAD0_opsz24.png\"); /* PNG/SVG \u2193 */\n"
"    width: 24px; height: 24px;                 /* \u0433\u0430\u0431\u0430\u0440\u0438\u0442\u044b \u0438\u043a\u043e\u043d\u043a\u0438              */\n"
"    margin: 0 auto;                            /* \u0446\u0435\u043d\u0442\u0440\u0438\u0440\u0443\u0435\u043c \u0432 \u0431\u043b\u043e\u043a\u0435           */\n"
"	transform: rotate(180deg);\n"
"}\n"
"\n"
"QSpinBox::down-arrow {\n"
"    image: url(\":/icon/arrow_drop_down_24dp_E3E3E3_FILL0_wght400_GRAD0_opsz24.png\"); /* PNG/SVG \u2193 */\n"
"    width: 24px; height: 24px;                 /* \u0433\u0430\u0431\u0430\u0440\u0438\u0442\u044b \u0438\u043a\u043e\u043d\u043a\u0438              */\n"
"    margin: 0 auto;                            "
                        "/* \u0446\u0435\u043d\u0442\u0440\u0438\u0440\u0443\u0435\u043c \u0432 \u0431\u043b\u043e\u043a\u0435           */\n"
"}\n"
"\n"
"\n"
"/* \u043e\u0442\u043a\u043b\u044e\u0447\u0430\u0435\u043c \u043a\u043d\u043e\u043f\u043a\u0438 \u0438 \u0438\u043a\u043e\u043d\u043a\u0438 \u043f\u0440\u0438 \u0434\u043e\u0441\u0442\u0438\u0436\u0435\u043d\u0438\u0438 min/max ---------------------*/\n"
"QSpinBox::up-button:disabled,\n"
"QSpinBox::down-button:disabled {\n"
"    background: #c8c8c8;                       /* \u0442\u0443\u0441\u043a\u043b\u044b\u0439 \u0444\u043e\u043d \u2014 \u043a\u043d\u043e\u043f\u043a\u0430 \u043d\u0435\u0430\u043a\u0442\u0438\u0432 */\n"
"}\n"
"\n"
"QSpinBox::up-arrow:disabled,\n"
"QSpinBox::down-arrow:disabled {\n"
"    image: none;                               /* \u043f\u0440\u044f\u0447\u0435\u043c \u0438\u043a\u043e\u043d\u043a\u0443 \u0443 \u043d\u0435\u0430\u043a\u0442\u0438\u0432\u043d\u043e\u0439   */\n"
"}\n"
"\n"
"/* \u0425\u041e\u0412\u0415\u0420 / \u0424\u041e\u041a\u0423\u0421"
                        " ---------------------------------------------------------*/\n"
"QSpinBox:hover  { background: #f9f9f9; }       /* \u043b\u0451\u0433\u043a\u043e\u0435 \u0432\u044b\u0441\u0432\u0435\u0442\u043b\u0435\u043d\u0438\u0435 \u043f\u0440\u0438 \u0445\u043e\u0432\u0435\u0440\u0435*/\n"
"QSpinBox:focus  { border: 1px solid #7aa9ff; } /* \u0441\u0438\u043d\u044f\u044f \u0440\u0430\u043c\u043a\u0430 \u043f\u0440\u0438 \u0444\u043e\u043a\u0443\u0441\u0435       */\n"
"\n"
"/* \u041e\u0422\u041a\u041b\u042e\u0427\u0401\u041d\u041d\u041e\u0415 \u0421\u041e\u0421\u0422\u041e\u042f\u041d\u0418\u0415 -------------------------------------------------*/\n"
"QSpinBox:disabled {\n"
"    color: #8f8f8f;                            /* \u043f\u0440\u0438\u0433\u043b\u0443\u0448\u0430\u0435\u043c \u0442\u0435\u043a\u0441\u0442             */\n"
"    background: #e0e0e0;                       /* \u0438 \u0444\u043e\u043d \u0432\u0441\u0435\u0433\u043e \u0432\u0438\u0434\u0436\u0435\u0442\u0430          */\n"
"}\n"
"\n"
"\n"
"\n"
"\n"
""
                        "\n"
"\n"
"")
        self.gridLayout_5 = QGridLayout(self.page_4)
        self.gridLayout_5.setObjectName(u"gridLayout_5")
        self.frame_9 = QFrame(self.page_4)
        self.frame_9.setObjectName(u"frame_9")
        self.frame_9.setMinimumSize(QSize(900, 820))
        self.frame_9.setBaseSize(QSize(1005, 787))
        self.frame_9.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_9.setFrameShadow(QFrame.Shadow.Raised)
        self.gridLayout_7 = QGridLayout(self.frame_9)
        self.gridLayout_7.setObjectName(u"gridLayout_7")
        self.frame_11 = QFrame(self.frame_9)
        self.frame_11.setObjectName(u"frame_11")
        self.frame_11.setMinimumSize(QSize(450, 0))
        self.frame_11.setMaximumSize(QSize(550, 500))
        self.frame_11.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.frame_11.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_11.setFrameShadow(QFrame.Shadow.Raised)
        self.gridLayout_8 = QGridLayout(self.frame_11)
        self.gridLayout_8.setObjectName(u"gridLayout_8")
        self.comboBox_7 = QComboBox(self.frame_11)
        self.comboBox_7.addItem("")
        self.comboBox_7.addItem("")
        self.comboBox_7.addItem("")
        self.comboBox_7.setObjectName(u"comboBox_7")
        sizePolicy2 = QSizePolicy(QSizePolicy.Policy.Expanding, QSizePolicy.Policy.Fixed)
        sizePolicy2.setHorizontalStretch(0)
        sizePolicy2.setVerticalStretch(0)
        sizePolicy2.setHeightForWidth(self.comboBox_7.sizePolicy().hasHeightForWidth())
        self.comboBox_7.setSizePolicy(sizePolicy2)
        self.comboBox_7.setMinimumSize(QSize(200, 40))
        self.comboBox_7.setLayoutDirection(Qt.LayoutDirection.LeftToRight)

        self.gridLayout_8.addWidget(self.comboBox_7, 3, 0, 1, 1)

        self.spinBox_2 = QSpinBox(self.frame_11)
        self.spinBox_2.setObjectName(u"spinBox_2")
        sizePolicy2.setHeightForWidth(self.spinBox_2.sizePolicy().hasHeightForWidth())
        self.spinBox_2.setSizePolicy(sizePolicy2)
        self.spinBox_2.setMinimumSize(QSize(0, 42))

        self.gridLayout_8.addWidget(self.spinBox_2, 5, 0, 1, 1)

        self.comboBox_5 = QComboBox(self.frame_11)
        self.comboBox_5.addItem("")
        self.comboBox_5.addItem("")
        self.comboBox_5.addItem("")
        self.comboBox_5.addItem("")
        self.comboBox_5.addItem("")
        self.comboBox_5.addItem("")
        self.comboBox_5.addItem("")
        self.comboBox_5.addItem("")
        self.comboBox_5.addItem("")
        self.comboBox_5.addItem("")
        self.comboBox_5.addItem("")
        self.comboBox_5.addItem("")
        self.comboBox_5.addItem("")
        self.comboBox_5.addItem("")
        self.comboBox_5.addItem("")
        self.comboBox_5.setObjectName(u"comboBox_5")
        sizePolicy2.setHeightForWidth(self.comboBox_5.sizePolicy().hasHeightForWidth())
        self.comboBox_5.setSizePolicy(sizePolicy2)
        self.comboBox_5.setMinimumSize(QSize(200, 40))
        self.comboBox_5.setLayoutDirection(Qt.LayoutDirection.LeftToRight)

        self.gridLayout_8.addWidget(self.comboBox_5, 1, 0, 1, 1)

        self.textBrowser_74 = QTextBrowser(self.frame_11)
        self.textBrowser_74.setObjectName(u"textBrowser_74")
        sizePolicy3 = QSizePolicy(QSizePolicy.Policy.Minimum, QSizePolicy.Policy.Expanding)
        sizePolicy3.setHorizontalStretch(0)
        sizePolicy3.setVerticalStretch(0)
        sizePolicy3.setHeightForWidth(self.textBrowser_74.sizePolicy().hasHeightForWidth())
        self.textBrowser_74.setSizePolicy(sizePolicy3)
        self.textBrowser_74.setMinimumSize(QSize(97, 44))
        self.textBrowser_74.setMaximumSize(QSize(16777215, 40))
        self.textBrowser_74.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_74.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.gridLayout_8.addWidget(self.textBrowser_74, 0, 0, 1, 2)

        self.verticalSpacer = QSpacerItem(20, 40, QSizePolicy.Policy.Minimum, QSizePolicy.Policy.Expanding)

        self.gridLayout_8.addItem(self.verticalSpacer, 7, 0, 1, 1)

        self.textBrowser_66 = QTextBrowser(self.frame_11)
        self.textBrowser_66.setObjectName(u"textBrowser_66")
        sizePolicy3.setHeightForWidth(self.textBrowser_66.sizePolicy().hasHeightForWidth())
        self.textBrowser_66.setSizePolicy(sizePolicy3)
        self.textBrowser_66.setMinimumSize(QSize(97, 0))
        self.textBrowser_66.setMaximumSize(QSize(16777215, 40))
        self.textBrowser_66.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_66.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.gridLayout_8.addWidget(self.textBrowser_66, 5, 1, 1, 1)

        self.textBrowser_65 = QTextBrowser(self.frame_11)
        self.textBrowser_65.setObjectName(u"textBrowser_65")
        sizePolicy3.setHeightForWidth(self.textBrowser_65.sizePolicy().hasHeightForWidth())
        self.textBrowser_65.setSizePolicy(sizePolicy3)
        self.textBrowser_65.setMinimumSize(QSize(97, 0))
        self.textBrowser_65.setMaximumSize(QSize(16777215, 40))
        self.textBrowser_65.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_65.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.gridLayout_8.addWidget(self.textBrowser_65, 4, 1, 1, 1)

        self.textBrowser_64 = QTextBrowser(self.frame_11)
        self.textBrowser_64.setObjectName(u"textBrowser_64")
        sizePolicy3.setHeightForWidth(self.textBrowser_64.sizePolicy().hasHeightForWidth())
        self.textBrowser_64.setSizePolicy(sizePolicy3)
        self.textBrowser_64.setMinimumSize(QSize(97, 0))
        self.textBrowser_64.setMaximumSize(QSize(16777215, 40))
        self.textBrowser_64.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_64.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.gridLayout_8.addWidget(self.textBrowser_64, 3, 1, 1, 1)

        self.textBrowser_63 = QTextBrowser(self.frame_11)
        self.textBrowser_63.setObjectName(u"textBrowser_63")
        sizePolicy3.setHeightForWidth(self.textBrowser_63.sizePolicy().hasHeightForWidth())
        self.textBrowser_63.setSizePolicy(sizePolicy3)
        self.textBrowser_63.setMinimumSize(QSize(97, 0))
        self.textBrowser_63.setMaximumSize(QSize(16777215, 40))
        self.textBrowser_63.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_63.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.gridLayout_8.addWidget(self.textBrowser_63, 2, 1, 1, 1)

        self.comboBox_6 = QComboBox(self.frame_11)
        self.comboBox_6.addItem("")
        self.comboBox_6.addItem("")
        self.comboBox_6.setObjectName(u"comboBox_6")
        sizePolicy2.setHeightForWidth(self.comboBox_6.sizePolicy().hasHeightForWidth())
        self.comboBox_6.setSizePolicy(sizePolicy2)
        self.comboBox_6.setMinimumSize(QSize(200, 40))
        self.comboBox_6.setLayoutDirection(Qt.LayoutDirection.LeftToRight)

        self.gridLayout_8.addWidget(self.comboBox_6, 2, 0, 1, 1)

        self.textBrowser_62 = QTextBrowser(self.frame_11)
        self.textBrowser_62.setObjectName(u"textBrowser_62")
        sizePolicy3.setHeightForWidth(self.textBrowser_62.sizePolicy().hasHeightForWidth())
        self.textBrowser_62.setSizePolicy(sizePolicy3)
        self.textBrowser_62.setMinimumSize(QSize(97, 0))
        self.textBrowser_62.setMaximumSize(QSize(16777215, 40))
        self.textBrowser_62.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_62.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.gridLayout_8.addWidget(self.textBrowser_62, 1, 1, 1, 1)

        self.comboBox_8 = QComboBox(self.frame_11)
        self.comboBox_8.addItem("")
        self.comboBox_8.addItem("")
        self.comboBox_8.setObjectName(u"comboBox_8")
        sizePolicy2.setHeightForWidth(self.comboBox_8.sizePolicy().hasHeightForWidth())
        self.comboBox_8.setSizePolicy(sizePolicy2)
        self.comboBox_8.setMinimumSize(QSize(200, 40))
        self.comboBox_8.setLayoutDirection(Qt.LayoutDirection.LeftToRight)

        self.gridLayout_8.addWidget(self.comboBox_8, 4, 0, 1, 1)

        self.spinBox_3 = QSpinBox(self.frame_11)
        self.spinBox_3.setObjectName(u"spinBox_3")
        sizePolicy2.setHeightForWidth(self.spinBox_3.sizePolicy().hasHeightForWidth())
        self.spinBox_3.setSizePolicy(sizePolicy2)
        self.spinBox_3.setMinimumSize(QSize(0, 42))

        self.gridLayout_8.addWidget(self.spinBox_3, 6, 0, 1, 1)

        self.textBrowser_67 = QTextBrowser(self.frame_11)
        self.textBrowser_67.setObjectName(u"textBrowser_67")
        sizePolicy3.setHeightForWidth(self.textBrowser_67.sizePolicy().hasHeightForWidth())
        self.textBrowser_67.setSizePolicy(sizePolicy3)
        self.textBrowser_67.setMinimumSize(QSize(97, 0))
        self.textBrowser_67.setMaximumSize(QSize(16777215, 40))
        self.textBrowser_67.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_67.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.gridLayout_8.addWidget(self.textBrowser_67, 6, 1, 1, 1)


        self.gridLayout_7.addWidget(self.frame_11, 0, 0, 1, 1)

        self.frame_12 = QFrame(self.frame_9)
        self.frame_12.setObjectName(u"frame_12")
        self.frame_12.setMinimumSize(QSize(529, 200))
        self.frame_12.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_12.setFrameShadow(QFrame.Shadow.Raised)
        self.gridLayout_14 = QGridLayout(self.frame_12)
        self.gridLayout_14.setObjectName(u"gridLayout_14")
        self.gridLayout_13 = QGridLayout()
        self.gridLayout_13.setObjectName(u"gridLayout_13")
        self.frame_22 = QFrame(self.frame_12)
        self.frame_22.setObjectName(u"frame_22")
        self.frame_22.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_22.setFrameShadow(QFrame.Shadow.Raised)

        self.gridLayout_13.addWidget(self.frame_22, 0, 0, 1, 1)

        self.pushButton_13 = QPushButton(self.frame_12)
        self.pushButton_13.setObjectName(u"pushButton_13")

        self.gridLayout_13.addWidget(self.pushButton_13, 0, 1, 1, 1)

        self.frame_24 = QFrame(self.frame_12)
        self.frame_24.setObjectName(u"frame_24")
        self.frame_24.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_24.setFrameShadow(QFrame.Shadow.Raised)

        self.gridLayout_13.addWidget(self.frame_24, 0, 2, 1, 1)


        self.gridLayout_14.addLayout(self.gridLayout_13, 0, 0, 1, 1)


        self.gridLayout_7.addWidget(self.frame_12, 1, 1, 1, 1)

        self.frame_13 = QFrame(self.frame_9)
        self.frame_13.setObjectName(u"frame_13")
        self.frame_13.setMinimumSize(QSize(450, 200))
        self.frame_13.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_13.setFrameShadow(QFrame.Shadow.Raised)
        self.textEditSP = QTextEdit(self.frame_13)
        self.textEditSP.setObjectName(u"textEditSP")
        self.textEditSP.setGeometry(QRect(10, 30, 321, 40))
        self.textEditSP.setStyleSheet(u"/* ----- QLineEdit / QTextEdit \u2014 \u00ab\u043a\u0430\u043a combobox\u00bb ------------------- */\n"
"QLineEdit,\n"
"QTextEdit {\n"
"    border: 1px solid #b4b4b4;\n"
"    border-radius: 12px;\n"
"    /* \u0441\u0442\u0440\u0435\u043b\u043a\u0438 \u043d\u0435\u0442 \u2013 \u0437\u043d\u0430\u0447\u0438\u0442 \u0445\u0432\u0430\u0442\u0438\u0442 \u043e\u0431\u044b\u0447\u043d\u043e\u0433\u043e \u043e\u0442\u0441\u0442\u0443\u043f\u0430 */\n"
"    padding: 4px 12px;\n"
"    background: #f4f4f4;\n"
"    min-height: 30px;\n"
"}\n"
"\n"
"/* \u0442\u0435 \u0436\u0435 \u0440\u0435\u0430\u043a\u0446\u0438\u0438 \u043d\u0430 hover / focus, \u0447\u0442\u043e \u0438 \u0443 \u043a\u043e\u043c\u0431\u043e\u0431\u043e\u043a\u0441\u0430 */\n"
"QLineEdit:hover,\n"
"QTextEdit:hover           { background: #f9f9f9; }\n"
"\n"
"QLineEdit:focus,\n"
"QTextEdit:focus           { border: 1px solid #7aa9ff; outline: none; }")
        self.pushButton_4 = QPushButton(self.frame_13)
        self.pushButton_4.setObjectName(u"pushButton_4")
        self.pushButton_4.setGeometry(QRect(10, 80, 431, 71))
        font = QFont()
        font.setFamilies([u"Noto Sans SC"])
        font.setPointSize(14)
        self.pushButton_4.setFont(font)
        self.textBrowser_73 = QTextBrowser(self.frame_13)
        self.textBrowser_73.setObjectName(u"textBrowser_73")
        self.textBrowser_73.setGeometry(QRect(340, 30, 97, 40))
        sizePolicy3.setHeightForWidth(self.textBrowser_73.sizePolicy().hasHeightForWidth())
        self.textBrowser_73.setSizePolicy(sizePolicy3)
        self.textBrowser_73.setMinimumSize(QSize(97, 0))
        self.textBrowser_73.setMaximumSize(QSize(16777215, 40))
        self.textBrowser_73.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_73.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.stackedWidget_2 = QStackedWidget(self.frame_13)
        self.stackedWidget_2.setObjectName(u"stackedWidget_2")
        self.stackedWidget_2.setGeometry(QRect(10, 160, 431, 101))
        self.stackedWidget_2.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.page_6 = QWidget()
        self.page_6.setObjectName(u"page_6")
        self.OS_update = QPushButton(self.page_6)
        self.OS_update.setObjectName(u"OS_update")
        self.OS_update.setEnabled(True)
        self.OS_update.setGeometry(QRect(0, 10, 431, 71))
        self.OS_update.setFont(font)
        self.stackedWidget_2.addWidget(self.page_6)
        self.page_9 = QWidget()
        self.page_9.setObjectName(u"page_9")
        self.textBrowser_83 = QTextBrowser(self.page_9)
        self.textBrowser_83.setObjectName(u"textBrowser_83")
        self.textBrowser_83.setGeometry(QRect(0, 20, 431, 61))
        sizePolicy3.setHeightForWidth(self.textBrowser_83.sizePolicy().hasHeightForWidth())
        self.textBrowser_83.setSizePolicy(sizePolicy3)
        self.textBrowser_83.setMinimumSize(QSize(0, 0))
        self.textBrowser_83.setMaximumSize(QSize(16777215, 16000))
        self.textBrowser_83.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_83.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.stackedWidget_2.addWidget(self.page_9)
        self.page_7 = QWidget()
        self.page_7.setObjectName(u"page_7")
        self.page_7.setContextMenuPolicy(Qt.ContextMenuPolicy.NoContextMenu)
        self.page_7.setLayoutDirection(Qt.LayoutDirection.RightToLeft)
        self.page_7.setStyleSheet(u"/* \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 \u041f\u0420\u041e\u0413\u0420\u0415\u0421\u0421-\u0411\u0410\u0420 \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 */\n"
"\n"
"/* \u00ab\u0437\u0430\u043f\u043e\u043b\u043d\u0435\u043d\u043d\u0430\u044f\u00bb \u0447\u0430\u0441\u0442\u044c (\u0433\u043e\u0440\u0438\u0437\u043e\u043d\u0442\u0430\u043b\u044c\u043d\u0430\u044f) */\n"
"QProgressBar::chunk {\n"
"    background: #2d97ff;         /* \u0432\u0430\u0448 \u0444\u0438\u0440\u043c\u0435\u043d\u043d\u044b\u0439 \u0441\u0438\u043d\u0438\u0439                 */\n"
"    border-radius: 12px;         /* \u0447\u0442\u043e\u0431\u044b \u043a\u0440\u0430\u0439 \u0437\u0430\u043f\u043e\u043b\u043d\u0435\u043d\u0438\u044f \u0442\u043e\u0436\u0435 \u0431\u044b\u043b \u043a\u0440\u0443\u0433\u043b\u044b\u043c */\n"
"	\n"
"}\n"
"\n"
"/* \u2500\u2500 QProgressBar \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500"
                        "\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500*/\n"
"QProgressBar {\n"
"    border: 2px solid #909090;   /* \u0442\u0430\u043a\u0430\u044f \u0436\u0435 \u0440\u0430\u043c\u043a\u0430, \u043a\u0430\u043a \u0432 \u0434\u0440\u0443\u0433\u0438\u0445 \u043a\u043e\u043d\u0442\u0440\u043e\u043b\u0430\u0445 */\n"
"    border-radius: 12px;\n"
"    background: #404040;         /* \u043e\u0431\u0449\u0438\u0439 \u0442\u0451\u043c\u043d\u043e-\u0441\u0435\u0440\u044b\u0439 \u0444\u043e\u043d */\n"
"    min-height: 24px;\n"
"\n"
"    text-align: center;          /* \u043f\u0440\u043e\u0446\u0435\u043d\u0442/\u0442\u0435\u043a\u0441\u0442 \u043f\u043e \u0446\u0435\u043d\u0442\u0440\u0443 */\n"
"    color: white;                /* \u0431\u0435\u043b\u044b\u0435 \u0431\u0443\u043a\u0432\u044b \u043f\u043e\u0432\u0435\u0440\u0445 \u0441\u0438\u043d\u0435\u0433\u043e */\n"
"}\n"
"")
        self.progressBar = QProgressBar(self.page_7)
        self.progressBar.setObjectName(u"progressBar")
        self.progressBar.setGeometry(QRect(10, 37, 411, 31))
        self.progressBar.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.progressBar.setValue(24)
        self.stackedWidget_2.addWidget(self.page_7)
        self.page_8 = QWidget()
        self.page_8.setObjectName(u"page_8")
        self.textBrowser_82 = QTextBrowser(self.page_8)
        self.textBrowser_82.setObjectName(u"textBrowser_82")
        self.textBrowser_82.setGeometry(QRect(0, 20, 431, 61))
        sizePolicy3.setHeightForWidth(self.textBrowser_82.sizePolicy().hasHeightForWidth())
        self.textBrowser_82.setSizePolicy(sizePolicy3)
        self.textBrowser_82.setMinimumSize(QSize(0, 0))
        self.textBrowser_82.setMaximumSize(QSize(16777215, 16000))
        self.textBrowser_82.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_82.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.stackedWidget_2.addWidget(self.page_8)

        self.gridLayout_7.addWidget(self.frame_13, 1, 0, 1, 1)

        self.frame_10 = QFrame(self.frame_9)
        self.frame_10.setObjectName(u"frame_10")
        sizePolicy4 = QSizePolicy(QSizePolicy.Policy.Minimum, QSizePolicy.Policy.Minimum)
        sizePolicy4.setHorizontalStretch(0)
        sizePolicy4.setVerticalStretch(0)
        sizePolicy4.setHeightForWidth(self.frame_10.sizePolicy().hasHeightForWidth())
        self.frame_10.setSizePolicy(sizePolicy4)
        self.frame_10.setMinimumSize(QSize(529, 455))
        self.frame_10.setMaximumSize(QSize(550, 500))
        self.frame_10.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_10.setFrameShadow(QFrame.Shadow.Raised)
        self.gridLayout_6 = QGridLayout(self.frame_10)
        self.gridLayout_6.setObjectName(u"gridLayout_6")
        self.stackedWidget_4 = QStackedWidget(self.frame_10)
        self.stackedWidget_4.setObjectName(u"stackedWidget_4")
        self.page_14 = QWidget()
        self.page_14.setObjectName(u"page_14")
        self.pushButton_8 = QPushButton(self.page_14)
        self.pushButton_8.setObjectName(u"pushButton_8")
        self.pushButton_8.setGeometry(QRect(100, 190, 311, 101))
        self.pushButton_8.setFont(font)
        self.stackedWidget_4.addWidget(self.page_14)
        self.page_15 = QWidget()
        self.page_15.setObjectName(u"page_15")
        self.textBrowser_12 = QTextBrowser(self.page_15)
        self.textBrowser_12.setObjectName(u"textBrowser_12")
        self.textBrowser_12.setGeometry(QRect(40, 50, 421, 121))
        self.textBrowser_12.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_12.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.pushButton_12 = QPushButton(self.page_15)
        self.pushButton_12.setObjectName(u"pushButton_12")
        self.pushButton_12.setGeometry(QRect(120, 270, 251, 81))
        font1 = QFont()
        font1.setFamilies([u"Noto Sans SC"])
        font1.setPointSize(12)
        self.pushButton_12.setFont(font1)
        self.stackedWidget_4.addWidget(self.page_15)
        self.page_16 = QWidget()
        self.page_16.setObjectName(u"page_16")
        self.textBrowser_13 = QTextBrowser(self.page_16)
        self.textBrowser_13.setObjectName(u"textBrowser_13")
        self.textBrowser_13.setGeometry(QRect(40, 30, 431, 121))
        self.textBrowser_13.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_13.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.pushButton_9 = QPushButton(self.page_16)
        self.pushButton_9.setObjectName(u"pushButton_9")
        self.pushButton_9.setGeometry(QRect(40, 180, 431, 71))
        self.pushButton_9.setFont(font)
        self.pushButton_10 = QPushButton(self.page_16)
        self.pushButton_10.setObjectName(u"pushButton_10")
        self.pushButton_10.setGeometry(QRect(40, 260, 431, 71))
        self.pushButton_10.setFont(font)
        self.stackedWidget_4.addWidget(self.page_16)
        self.page_17 = QWidget()
        self.page_17.setObjectName(u"page_17")
        self.textBrowser_14 = QTextBrowser(self.page_17)
        self.textBrowser_14.setObjectName(u"textBrowser_14")
        self.textBrowser_14.setGeometry(QRect(40, 30, 431, 121))
        self.textBrowser_14.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_14.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.pushButton_14 = QPushButton(self.page_17)
        self.pushButton_14.setObjectName(u"pushButton_14")
        self.pushButton_14.setGeometry(QRect(40, 180, 431, 71))
        self.pushButton_14.setFont(font)
        self.pushButton_15 = QPushButton(self.page_17)
        self.pushButton_15.setObjectName(u"pushButton_15")
        self.pushButton_15.setGeometry(QRect(40, 260, 431, 71))
        self.pushButton_15.setFont(font)
        self.stackedWidget_4.addWidget(self.page_17)

        self.gridLayout_6.addWidget(self.stackedWidget_4, 0, 0, 1, 1)


        self.gridLayout_7.addWidget(self.frame_10, 0, 1, 1, 1)


        self.gridLayout_5.addWidget(self.frame_9, 0, 0, 1, 1)

        self.stackedWidget.addWidget(self.page_4)
        self.page_3 = QWidget()
        self.page_3.setObjectName(u"page_3")
        self.page_3.setStyleSheet(u"/* ===== QComboBox: \u043f\u043e\u043b\u043d\u044b\u0439 \u0441\u0442\u0438\u043b\u044c \u0431\u0435\u0437 \u0440\u0435\u0441\u0443\u0440\u0441\u043e\u0432 ===== */\n"
"QFrame#qt_combo_box_popup {\n"
"    background: transparent;   /* \u2190 \u0444\u043e\u043d \u043f\u043e\u043b\u043d\u043e\u0441\u0442\u044c\u044e \u201c\u0434\u044b\u0440\u044f\u0432\u044b\u0439\u201d */\n"
"    border: none;\n"
"    border-radius: 12px;\n"
"}\n"
"\n"
"\n"
"/* \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 \u0432\u0435\u0440\u0442\u0438\u043a\u0430\u043b\u044c\u043d\u044b\u0439 \u0441\u043a\u0440\u043e\u043b\u043b\u0431\u0430\u0440 \u0432\u043d\u0443\u0442\u0440\u0438 \u0432\u044b\u043f\u0430\u0434\u0430\u044e\u0449\u0435\u0433\u043e \u0441\u043f\u0438\u0441\u043a\u0430 \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 */\n"
"QComboBox QAbstractItemView QScrollBar:vertical {\n"
"    width: 12px;               /* \u0442\u043e\u043b\u0449\u0438\u043d\u0430 \u0432\u0441\u0435\u0439 \u043f\u043e\u043b\u043e"
                        "\u0441\u044b \u043f\u0440\u043e\u043a\u0440\u0443\u0442\u043a\u0438          */\n"
"    margin: 0px 0px 0px 0;     /* \u043b\u0451\u0433\u043a\u0438\u0439 \u043e\u0442\u0441\u0442\u0443\u043f \u043e\u0442 \u043f\u0440\u0430\u0432\u043e\u0439 \u0433\u0440\u0430\u043d\u0438 \u0441\u043f\u0438\u0441\u043a\u0430   */\n"
"    background: #ffffff;   /* \u2190 \u0443\u0431\u0438\u0440\u0430\u0435\u043c \u0444\u043e\u043d \u0441\u0430\u043c\u043e\u0439 \u043f\u043e\u043b\u043e\u0441\u044b             */\n"
"    border: none;              /* \u0438 \u0440\u0430\u043c\u043a\u0443, \u043a\u043e\u0442\u043e\u0440\u0443\u044e Qt \u0440\u0438\u0441\u0443\u0435\u0442 \u043f\u043e \u0443\u043c\u043e\u043b\u0447\u0430\u043d\u0438\u044e*/\n"
"}\n"
"\n"
"/* track (\u043a\u043e\u043b\u0435\u044f). \u0414\u0435\u043b\u0430\u0435\u043c \u0435\u0451 \u043d\u0435\u0432\u0438\u0434\u0438\u043c\u043e\u0439 \u2014 \u043e\u0441\u0442\u0430\u0451\u0442\u0441\u044f \u00ab\u043f\u0443\u0441\u0442\u043e\u0435 \u043c\u0435\u0441\u0442\u043e\u00bb"
                        " */\n"
"QComboBox QAbstractItemView QScrollBar::groove:vertical {\n"
"    background: #ffffff;   /* \u043d\u0438\u043a\u0430\u043a\u043e\u0433\u043e \u0446\u0432\u0435\u0442\u0430                         */\n"
"    border: none;\n"
"    margin: 0;                 /* \u0432\u0430\u0436\u043d\u043e! \u0443\u0431\u0438\u0440\u0430\u0435\u0442 \u0432\u043d\u0443\u0442\u0440\u0435\u043d\u043d\u0438\u0435 \u00ab\u043f\u043e\u043b\u044f\u00bb Qt    */\n"
"}\n"
"\n"
"/* \u043f\u0443\u0441\u0442\u044b\u0435 \u0443\u0447\u0430\u0441\u0442\u043a\u0438 \u043d\u0430\u0434 \u0438 \u043f\u043e\u0434 \u043f\u043e\u043b\u0437\u0443\u043d\u043a\u043e\u043c \u2014 \u0442\u043e\u0436\u0435 \u0432 \u043d\u043e\u043b\u044c */\n"
"QComboBox QAbstractItemView QScrollBar::add-page:vertical,\n"
"QComboBox QAbstractItemView QScrollBar::sub-page:vertical {\n"
"    background: #ffffff;\n"
"    border: none;\n"
"}\n"
"\n"
"/* \u0441\u0430\u043c \u043f\u043e\u043b\u0437\u0443\u043d\u043e\u043a (\u00ab\u043e\u0432\u0430\u043b\u00bb) --------"
                        "-----------------------------------------*/\n"
"QComboBox QAbstractItemView QScrollBar::handle:vertical {\n"
"    background: #808080;       /* \u0446\u0432\u0435\u0442 \u00ab\u0442\u0430\u0431\u043b\u0435\u0442\u043a\u0438\u00bb                        */\n"
"    border-radius: 999px;        /* \u0441\u043a\u0440\u0443\u0433\u043b\u044f\u0435\u043c \u043a\u0440\u0430\u044f \u043f\u043e \u043f\u043e\u043b\u043d\u043e\u0439               */\n"
"    min-height: 24px;          /* \u0447\u0442\u043e\u0431\u044b \u043d\u0435 \u0438\u0441\u0447\u0435\u0437\u0430\u043b \u043f\u0440\u0438 \u043c\u0430\u043b\u0435\u043d\u044c\u043a\u043e\u043c \u043a\u043e\u043d\u0442\u0435\u043d\u0442\u0435*/\n"
"    margin: 2px;               /* \u0437\u0430\u0437\u043e\u0440 \u043e\u0442 \u0433\u0440\u0430\u043d\u0438\u0446 \u0431\u0430\u0440\u0430                   */\n"
"}\n"
"\n"
"QComboBox QAbstractItemView QScrollBar::sub-line:vertical,   /* \u0432\u0435\u0440\u0445\u043d\u044f\u044f  */\n"
"QComboBox QAbstractItemView QScrollBa"
                        "r::add-line:vertical {  /* \u043d\u0438\u0436\u043d\u044f\u044f   */\n"
"    height: 0px;                /* \u0443\u0431\u0438\u0440\u0430\u0435\u043c \u0432\u0438\u0434\u0438\u043c\u0443\u044e \u0447\u0430\u0441\u0442\u044c      */\n"
"    width:  0px;\n"
"    border: none;\n"
"    background: #ffffff;\n"
"    subcontrol-origin: margin;  /* \u0447\u0442\u043e\u0431\u044b \u043d\u0435 \u0437\u0430\u043d\u0438\u043c\u0430\u043b\u0438 \u043c\u0435\u0441\u0442\u043e    */\n"
"}\n"
"\n"
"/* \u2500\u2500 \u0435\u0441\u043b\u0438 \u0432\u0434\u0440\u0443\u0433 \u043f\u043e\u044f\u0432\u0438\u0442\u0441\u044f \u0433\u043e\u0440\u0438\u0437\u043e\u043d\u0442\u0430\u043b\u044c\u043d\u044b\u0439 \u0441\u043a\u0440\u043e\u043b\u043b\u0431\u0430\u0440 \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500*/\n"
"QComboBox QAbstractItemView QScrollBar::sub-line:horizontal, /* \u043b\u0435\u0432\u0430\u044f    */\n"
"QComboBox QAbstractItemView QScrollBa"
                        "r::add-line:horizontal { /* \u043f\u0440\u0430\u0432\u0430\u044f  */\n"
"    width:  0px;\n"
"    height: 0px;\n"
"    border: none;\n"
"    background: #ffffff;\n"
"    subcontrol-origin: margin;\n"
"}\n"
"\n"
"/* \u041e\u0421\u041d\u041e\u0412\u041d\u041e\u0415 \u041f\u041e\u041b\u0415 -----------------------------------------------------------*/\n"
"QComboBox {\n"
"    border: 1px solid #b4b4b4;\n"
"    border-radius: 12px;\n"
"    padding: 4px 40px 4px 12px;   /* \u043c\u0435\u0441\u0442\u043e \u043f\u043e\u0434 \u0441\u0442\u0440\u0435\u043b\u043a\u0443 \u0441\u043f\u0440\u0430\u0432\u0430 */\n"
"    background: #f4f4f4;\n"
"    min-height: 60px;             /* \u0447\u0442\u043e\u0431\u044b \u043d\u0435 \u0441\u043f\u043b\u044e\u0449\u0438\u0432\u0430\u043b\u0441\u044f */\n"
"combobox-popup: 0;   \n"
"}\n"
"\n"
"/* \u041a\u041d\u041e\u041f\u041a\u0410 \u0412\u042b\u041f\u0410\u0414\u0410\u041d\u0418\u042f (\u043f\u0440\u0430\u0432\u044b\u0439 \u0441\u0435\u0433\u043c\u0435\u043d\u0442) ------------------"
                        "--------------------*/\n"
"QComboBox::drop-down {\n"
"    subcontrol-origin: padding;\n"
"    subcontrol-position: top right;\n"
"    width: 32px;\n"
"    border-left: 1px solid #b4b4b4;\n"
"    border-top-right-radius: 12px;\n"
"    border-bottom-right-radius: 12px;\n"
"    background: #e2e2e2;\n"
"}\n"
"\n"
"QComboBox::drop-down { \n"
"    background: #808080;   /* \u0432\u0440\u0435\u043c\u0435\u043d\u043d\u043e! */\n"
"}\n"
"\n"
"/* \u0421\u0422\u0420\u0415\u041b\u041a\u0410 ----------------------------------------------------------------*/\n"
"QComboBox::down-arrow {\n"
"image: url(\":/icon/arrow_drop_down_24dp_E3E3E3_FILL0_wght400_GRAD0_opsz24.png\");\n"
"    width: 24px;      /* \u043f\u043e\u0434\u0433\u043e\u043d\u0438 \u043f\u043e\u0434 \u0440\u0435\u0430\u043b\u044c\u043d\u044b\u0439 \u0440\u0430\u0437\u043c\u0435\u0440 PNG */\n"
"    height: 24px;\n"
"    margin: 0 auto;   /* \u043f\u043e \u0446\u0435\u043d\u0442\u0440\u0443 \u043a\u043d\u043e\u043f\u043a\u0438 drop\u2011down */\n"
"    border: non"
                        "e;     /* \u0433\u043b\u0443\u0448\u0438\u043c \u0432\u0441\u044f\u043a\u0438\u0435 \u0441\u0442\u0430\u0440\u044b\u0435 \u0433\u0440\u0430\u043d\u0438\u0446\u044b */\n"
"}\n"
"\n"
"/* \u041f\u043e\u0432\u043e\u0440\u043e\u0442 \u043f\u0440\u0438 \u0440\u0430\u0441\u043a\u0440\u044b\u0442\u0438\u0438 --------------------------------------------------*/\n"
"QComboBox::down-arrow:on {\n"
"    transform: rotate(180deg);\n"
"}\n"
"\n"
"\n"
"\n"
"\n"
"\n"
"/* \u0425\u041e\u0412\u0415\u0420/\u0424\u041e\u041a\u0423\u0421 -------------------------------------------------------------*/\n"
"QComboBox:hover { background: #f9f9f9; }\n"
"\n"
"QComboBox:focus {\n"
"    border: 1px solid #7aa9ff;\n"
"    outline: none;\n"
"}\n"
"\n"
"/* \u0412\u042b\u041f\u0410\u0414\u0410\u042e\u0429\u0418\u0419 \u0421\u041f\u0418\u0421\u041e\u041a -----------------------------------------------------*/\n"
"QComboBox QAbstractItemView {\n"
"    /* \u0442\u043e\u0442 \u0436\u0435 \u0440\u0430\u0434\u0438\u0443\u0441, \u0447\u0442\u043e \u0443"
                        " \u043f\u043e\u043b\u044f */\n"
"    border: 1px solid #c8c8c8;\n"
"    border-radius: 12px;\n"
"    padding: 4px;                       /* \u043b\u0451\u0433\u043a\u0438\u0439 \u00ab\u043e\u0442\u0441\u0442\u0443\u043f-\u0440\u0430\u043c\u043a\u0430\u00bb \u0432\u043d\u0443\u0442\u0440\u0438 */\n"
"    background: #FFFFFF;\n"
"\n"
"    /* \u043e\u0442\u043a\u043b\u044e\u0447\u0430\u0435\u043c \u0441\u0442\u0430\u043d\u0434\u0430\u0440\u0442\u043d\u044b\u0439 dotted focus-rectangle */\n"
"    outline: 0;                         /* Qt >5.12 \u043f\u043e\u043d\u0438\u043c\u0430\u0435\u0442 outline */\n"
"    /* \u0435\u0441\u043b\u0438 outline \u043d\u0435 \u0440\u0430\u0431\u043e\u0442\u0430\u0435\u0442 \u0432 \u0432\u0430\u0448\u0435\u0439 \u0432\u0435\u0440\u0441\u0438\u0438:\n"
"       border: none; */\n"
"}\n"
"\n"
"\n"
"QComboBox QAbstractItemView::viewport {\n"
"    border-radius: 8px;\n"
"    background: transparent;\n"
"}\n"
"\n"
"/* \u0441\u0442\u0440\u043e\u043a\u0438 \u0432\u043d\u0443\u0442\u0440\u0438"
                        " \u0441\u043f\u0438\u0441\u043a\u0430 */\n"
"QComboBox QAbstractItemView::item {\n"
"    padding: 6px 12px;\n"
"    border-radius: 6px;                 /* \u043b\u0451\u0433\u043a\u043e\u0435 \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 hover/selected */\n"
"}\n"
"\n"
"/* \u043f\u043e\u0434\u0441\u0432\u0435\u0442\u043a\u0430 \u043d\u0430\u0432\u0435\u0434\u0435\u043d\u0438\u044f  */\n"
"QComboBox QAbstractItemView::item:hover {\n"
"    background: #f0f0f0;\n"
"}\n"
"\n"
"/* \u0432\u044b\u0431\u0440\u0430\u043d\u043d\u044b\u0439 \u044d\u043b\u0435\u043c\u0435\u043d\u0442 (\u0431\u0435\u0437 \u043f\u0443\u043d\u043a\u0442\u0438\u0440\u0430!) */\n"
"QComboBox QAbstractItemView::item:selected {\n"
"    background: #2d97ff;                /* \u043f\u0440\u0438\u043c\u0435\u0440 \u0430\u043a\u0442\u0438\u0432\u043d\u043e\u0433\u043e \u0446\u0432\u0435\u0442\u0430 */\n"
"    color: #ffffff;\n"
"    outline: 0;                         /* \u0441\u0442\u0440\u0430\u0445\u043e\u0432\u043a\u0430 */\n"
"  "
                        "  /* \u0438\u043b\u0438 border: none;  -> \u0435\u0441\u043b\u0438 outline \u043d\u0435 \u043f\u043e\u0434\u0434\u0435\u0440\u0436\u0438\u0432\u0430\u0435\u0442\u0441\u044f */\n"
"}\n"
"\n"
"/* \u041e\u0444\u043e\u0440\u043c\u043b\u0435\u043d\u0438\u0435 \u0442\u0435\u043a\u0441\u0442\u0430 \u0438 \u0440\u0430\u043c\u043a\u0438 \u0434\u043b\u044f QLabel \u0438 QTextBrowser */\n"
"QLabel,\n"
"QTextBrowser {\n"
"    color: white;                    /* \u0446\u0432\u0435\u0442 \u0448\u0440\u0438\u0444\u0442\u0430 */\n"
"    border-radius: 10px;             /* \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 \u0443\u0433\u043b\u043e\u0432 \u0440\u0430\u043c\u043a\u0438 */\n"
"    padding: 6px;                    /* \u0432\u043d\u0443\u0442\u0440\u0435\u043d\u043d\u0438\u0435 \u043e\u0442\u0441\u0442\u0443\u043f\u044b */\n"
"border: 2px solid #909090; \n"
"}\n"
"\n"
"\n"
"/* \u041d\u043e\u0440\u043c\u0430\u043b\u044c\u043d\u043e\u0435 \u0441\u043e\u0441\u0442\u043e\u044f\u043d\u0438\u0435 */\n"
"QPushBu"
                        "tton {\n"
"    background-color: #404040;        /* \u0437\u0430\u043b\u0438\u0432\u043a\u0430 */\n"
"    color: white;                     /* \u0446\u0432\u0435\u0442 \u0442\u0435\u043a\u0441\u0442\u0430 */\n"
"    border: 2px solid #909090;        /* \u0442\u043e\u043b\u0449\u0438\u043d\u0430 \u0438 \u0446\u0432\u0435\u0442 \u043e\u0431\u0432\u043e\u0434\u043a\u0438 */\n"
"    border-radius: 12px;              /* \u0440\u0430\u0434\u0438\u0443\u0441 \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u044f */\n"
"    padding: 6px 12px;                /* \u00ab\u0432\u043e\u0437\u0434\u0443\u0445\u00bb \u0432\u043d\u0443\u0442\u0440\u0438 */\n"
"}\n"
"\n"
"/* \u041a\u0443\u0440\u0441\u043e\u0440 \u043d\u0430\u0432\u0435\u0434\u0451\u043d */\n"
"QPushButton:hover {\n"
"    background-color: #505050;\n"
"    border-color: #707070;\n"
"}\n"
"\n"
"/* \u041a\u043d\u043e\u043f\u043a\u0430 \u043d\u0430\u0436\u0430\u0442\u0430 (\u0443\u0434\u0435\u0440\u0436\u0438\u0432\u0430\u0435\u0442\u0441\u044f) */\n"
"QPushB"
                        "utton:pressed {\n"
"    background-color: #909090;\n"
"    border-color: #909090;\n"
"}\n"
"\n"
"/* QLabel \u0438\u043b\u0438 QTextBrowser */\n"
"QLabel, QTextBrowser {\n"
"    border: 2px solid #909090;   /* \u0442\u043e\u043b\u0449\u0438\u043d\u0430 \u0438 \u0446\u0432\u0435\u0442 */\n"
"    border-radius: 10px;         /* \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 */\n"
"    padding: 6px;                /* \u0432\u043d\u0443\u0442\u0440\u0435\u043d\u043d\u0438\u0435 \u043e\u0442\u0441\u0442\u0443\u043f\u044b */\n"
"    color: white;              /* \u0446\u0432\u0435\u0442 \u0448\u0440\u0438\u0444\u0442\u0430 */\n"
"}\n"
"\n"
"/* ===== QSpinBox \u2014 \u0441\u0442\u0438\u043b\u044c \u043f\u043e\u0434 QComboBox (\u043a\u0430\u0436\u0434\u044b\u0439 \u043f\u0430\u0440\u0430\u043c\u0435\u0442\u0440 \u043f\u043e\u0434\u043f\u0438\u0441\u0430\u043d) ===== */\n"
"\n"
"/* \u041e\u0421\u041d\u041e\u0412\u041d\u041e\u0415 \u041f\u041e\u041b\u0415 ----------------------------------------------------"
                        "-----*/\n"
"QSpinBox {\n"
"    border: 1px solid #b4b4b4;                 /* \u0432\u043d\u0435\u0448\u043d\u044f\u044f \u0440\u0430\u043c\u043a\u0430 \u0432\u0438\u0434\u0436\u0435\u0442\u0430        */\n"
"    border-radius: 12px;                       /* \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 \u0432\u0441\u0435\u0445 \u0443\u0433\u043b\u043e\u0432        */\n"
"\n"
"    padding-left: 12px;                        /* \u043e\u0442\u0441\u0442\u0443\u043f \u0442\u0435\u043a\u0441\u0442\u0430 \u0441\u043b\u0435\u0432\u0430          */\n"
"    padding-right: 40px;                       /* \u0440\u0435\u0437\u0435\u0440\u0432 \u043f\u043e\u0434 \u0431\u043b\u043e\u043a \u0441\u0442\u0440\u0435\u043b\u043e\u043a      */\n"
"    background: #f4f4f4;                       /* \u0444\u043e\u043d \u043f\u043e\u043b\u044f \u0432\u0432\u043e\u0434\u0430               */\n"
"    min-height: 60px;                          /* \u043c\u0438\u043d\u0438\u043c\u0430\u043b\u044c\u043d\u0430\u044f \u0432\u044b"
                        "\u0441\u043e\u0442\u0430 \u043a\u043e\u043d\u0442\u0440\u043e\u043b\u0430  */\n"
"    color: black;                              /* \u0446\u0432\u0435\u0442 \u0432\u0432\u0435\u0434\u0451\u043d\u043d\u043e\u0433\u043e \u0442\u0435\u043a\u0441\u0442\u0430       */\n"
"\n"
"    outline: none;                             /* \u0443\u0431\u0438\u0440\u0430\u0435\u043c \u0441\u0442\u0430\u043d\u0434\u0430\u0440\u0442\u043d\u044b\u0439 \u043f\u0443\u043d\u043a\u0442\u0438p  */\n"
"}\n"
"\n"
"/* \u0411\u041b\u041e\u041a \u0421\u0422\u0420\u0415\u041b\u041e\u041a ----------------------------------------------------------*/\n"
"/* \u043e\u0431\u0449\u0438\u0435 \u043f\u0430\u0440\u0430\u043c\u0435\u0442\u0440\u044b \u0434\u043b\u044f \u043e\u0431\u0435\u0438\u0445 \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u043e\u043a \u0431\u043b\u043e\u043a\u0430 */\n"
"QSpinBox::up-button,\n"
"QSpinBox::down-button {\n"
"    subcontrol-origin: padding;                /* \u043a\u043e\u043e\u0440\u0434\u0438\u043d\u0430\u0442\u044b \u043e"
                        "\u0442 padding-box    */\n"
"    width: 32px;                               /* \u0448\u0438\u0440\u0438\u043d\u0430 \u0441\u0435\u0433\u043c\u0435\u043d\u0442\u0430 \u0441\u043e \u0441\u0442\u0440\u0435\u043b\u043a\u0430\u043c\u0438 */\n"
"    border-left: 1px solid #b4b4b4;            /* \u043b\u0438\u043d\u0438\u044f-\u0440\u0430\u0437\u0434\u0435\u043b\u0438\u0442\u0435\u043b\u044c \u0441\u043b\u0435\u0432\u0430      */\n"
"    background: #808080;                       /* \u0444\u043e\u043d \u0431\u043b\u043e\u043a\u0430 \u0441\u0442\u0440\u0435\u043b\u043e\u043a            */\n"
"}\n"
"\n"
"/* \u2193 \u043d\u0438\u0436\u043d\u044f\u044f \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u0430 \u0431\u043b\u043e\u043a\u0430 \u0441\u0442\u0440\u0435\u043b\u043e\u043a --------------------------------------*/\n"
"QSpinBox::down-button {\n"
"    subcontrol-position: bottom right;         /* \u043f\u0440\u0438\u0432\u044f\u0437\u043a\u0430 \u043a \u043f\u0440\u0430\u0432\u043e\u043c\u0443-\u043d\u0438\u0436\u043d\u0435"
                        "\u043c\u0443   */\n"
"    height: 30%;                               /* \u0437\u0430\u043d\u0438\u043c\u0430\u0435\u043c \u043e\u0441\u0442\u0430\u0432\u0448\u0438\u0435\u0441\u044f 50 %     */\n"
"    border-bottom-right-radius: 12px;          /* \u0441\u043a\u0440\u0443\u0433\u043b\u044f\u0435\u043c \u0422\u041e\u041b\u042c\u041a\u041e \u043d\u0438\u0437-\u043f\u0440\u0430\u0432.   */\n"
"}\n"
"\n"
"\n"
"/* \u2191 \u0432\u0435\u0440\u0445\u043d\u044f\u044f \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u0430 \u0431\u043b\u043e\u043a\u0430 \u0441\u0442\u0440\u0435\u043b\u043e\u043a -------------------------------------*/\n"
"QSpinBox::up-button {\n"
"    subcontrol-position: top right;            /* \u043f\u0440\u0438\u0432\u044f\u0437\u043a\u0430 \u043a \u043f\u0440\u0430\u0432\u043e\u043c\u0443-\u0432\u0435\u0440\u0445\u043d\u0435\u043c\u0443  */\n"
"    height: 30%;                               /* \u0437\u0430\u043d\u0438\u043c\u0430\u0435\u043c \u0440\u043e\u0432\u043d\u043e \u043f\u043e\u043b\u043e\u0432\u0438"
                        "\u043d\u0443 \u0432\u044b\u0441. */\n"
"    border-top-right-radius: 12px;             /* \u0441\u043a\u0440\u0443\u0433\u043b\u044f\u0435\u043c \u0422\u041e\u041b\u042c\u041a\u041e \u0432\u0435\u0440\u0445-\u043f\u0440\u0430\u0432.  */\n"
"}\n"
"\n"
"/* \u0432\u0438\u0437\u0443\u0430\u043b\u044c\u043d\u044b\u0439 \u043e\u0442\u043a\u043b\u0438\u043a \u043f\u0440\u0438 \u043d\u0430\u0436\u0430\u0442\u0438\u0438 ----------------------------------------*/\n"
"QSpinBox::up-button:pressed,\n"
"QSpinBox::down-button:pressed {\n"
"    background: #6d6d6d;                       /* \u0437\u0430\u0442\u0435\u043c\u043d\u044f\u0435\u043c \u0444\u043e\u043d \u043d\u0430 \u0432\u0440\u0435\u043c\u044f \u043a\u043b\u0438\u043a\u0430 */\n"
"}\n"
"\n"
"/* \u0421\u0422\u0420\u0415\u041b\u041a\u0418 (\u0438\u043a\u043e\u043d\u043a\u0438) ------------------------------------------------------*/\n"
"QSpinBox::up-arrow {\n"
"    image: url(\":/icon/arrow_drop_up_24dp_E3E3E3_FILL0_wght400_GRAD0_opsz24.png\"); /* PNG/SVG \u2193 */\n"
""
                        "    width: 24px; height: 24px;                 /* \u0433\u0430\u0431\u0430\u0440\u0438\u0442\u044b \u0438\u043a\u043e\u043d\u043a\u0438              */\n"
"    margin: 0 auto;                            /* \u0446\u0435\u043d\u0442\u0440\u0438\u0440\u0443\u0435\u043c \u0432 \u0431\u043b\u043e\u043a\u0435           */\n"
"	transform: rotate(180deg);\n"
"}\n"
"\n"
"QSpinBox::down-arrow {\n"
"    image: url(\":/icon/arrow_drop_down_24dp_E3E3E3_FILL0_wght400_GRAD0_opsz24.png\"); /* PNG/SVG \u2193 */\n"
"    width: 24px; height: 24px;                 /* \u0433\u0430\u0431\u0430\u0440\u0438\u0442\u044b \u0438\u043a\u043e\u043d\u043a\u0438              */\n"
"    margin: 0 auto;                            /* \u0446\u0435\u043d\u0442\u0440\u0438\u0440\u0443\u0435\u043c \u0432 \u0431\u043b\u043e\u043a\u0435           */\n"
"}\n"
"\n"
"\n"
"/* \u043e\u0442\u043a\u043b\u044e\u0447\u0430\u0435\u043c \u043a\u043d\u043e\u043f\u043a\u0438 \u0438 \u0438\u043a\u043e\u043d\u043a\u0438 \u043f\u0440\u0438 \u0434\u043e\u0441\u0442\u0438"
                        "\u0436\u0435\u043d\u0438\u0438 min/max ---------------------*/\n"
"QSpinBox::up-button:disabled,\n"
"QSpinBox::down-button:disabled {\n"
"    background: #c8c8c8;                       /* \u0442\u0443\u0441\u043a\u043b\u044b\u0439 \u0444\u043e\u043d \u2014 \u043a\u043d\u043e\u043f\u043a\u0430 \u043d\u0435\u0430\u043a\u0442\u0438\u0432 */\n"
"}\n"
"\n"
"QSpinBox::up-arrow:disabled,\n"
"QSpinBox::down-arrow:disabled {\n"
"    image: none;                               /* \u043f\u0440\u044f\u0447\u0435\u043c \u0438\u043a\u043e\u043d\u043a\u0443 \u0443 \u043d\u0435\u0430\u043a\u0442\u0438\u0432\u043d\u043e\u0439   */\n"
"}\n"
"\n"
"/* \u0425\u041e\u0412\u0415\u0420 / \u0424\u041e\u041a\u0423\u0421 ---------------------------------------------------------*/\n"
"QSpinBox:hover  { background: #f9f9f9; }       /* \u043b\u0451\u0433\u043a\u043e\u0435 \u0432\u044b\u0441\u0432\u0435\u0442\u043b\u0435\u043d\u0438\u0435 \u043f\u0440\u0438 \u0445\u043e\u0432\u0435\u0440\u0435*/\n"
"QSpinBox:focus  { border: 1px solid #7aa9f"
                        "f; } /* \u0441\u0438\u043d\u044f\u044f \u0440\u0430\u043c\u043a\u0430 \u043f\u0440\u0438 \u0444\u043e\u043a\u0443\u0441\u0435       */\n"
"\n"
"/* \u041e\u0422\u041a\u041b\u042e\u0427\u0401\u041d\u041d\u041e\u0415 \u0421\u041e\u0421\u0422\u041e\u042f\u041d\u0418\u0415 -------------------------------------------------*/\n"
"QSpinBox:disabled {\n"
"    color: #8f8f8f;                            /* \u043f\u0440\u0438\u0433\u043b\u0443\u0448\u0430\u0435\u043c \u0442\u0435\u043a\u0441\u0442             */\n"
"    background: #e0e0e0;                       /* \u0438 \u0444\u043e\u043d \u0432\u0441\u0435\u0433\u043e \u0432\u0438\u0434\u0436\u0435\u0442\u0430          */\n"
"}\n"
"\n"
"")
        self.gridLayout_2 = QGridLayout(self.page_3)
        self.gridLayout_2.setObjectName(u"gridLayout_2")
        self.frame_7 = QFrame(self.page_3)
        self.frame_7.setObjectName(u"frame_7")
        self.frame_7.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_7.setFrameShadow(QFrame.Shadow.Raised)

        self.gridLayout_2.addWidget(self.frame_7, 6, 0, 1, 1)

        self.comboBox_2 = QComboBox(self.page_3)
        self.comboBox_2.addItem("")
        self.comboBox_2.setObjectName(u"comboBox_2")
        sizePolicy5 = QSizePolicy(QSizePolicy.Policy.Preferred, QSizePolicy.Policy.Maximum)
        sizePolicy5.setHorizontalStretch(0)
        sizePolicy5.setVerticalStretch(0)
        sizePolicy5.setHeightForWidth(self.comboBox_2.sizePolicy().hasHeightForWidth())
        self.comboBox_2.setSizePolicy(sizePolicy5)
        self.comboBox_2.setMinimumSize(QSize(0, 70))
        self.comboBox_2.setFont(font)
        self.comboBox_2.setLayoutDirection(Qt.LayoutDirection.LeftToRight)

        self.gridLayout_2.addWidget(self.comboBox_2, 2, 1, 1, 1)

        self.frame_8 = QFrame(self.page_3)
        self.frame_8.setObjectName(u"frame_8")
        self.frame_8.setMinimumSize(QSize(400, 60))
        self.frame_8.setFrameShape(QFrame.Shape.StyledPanel)
        self.frame_8.setFrameShadow(QFrame.Shadow.Raised)

        self.gridLayout_2.addWidget(self.frame_8, 6, 1, 1, 1)

        self.spinBox = QSpinBox(self.page_3)
        self.spinBox.setObjectName(u"spinBox")
        sizePolicy6 = QSizePolicy(QSizePolicy.Policy.Minimum, QSizePolicy.Policy.Maximum)
        sizePolicy6.setHorizontalStretch(0)
        sizePolicy6.setVerticalStretch(0)
        sizePolicy6.setHeightForWidth(self.spinBox.sizePolicy().hasHeightForWidth())
        self.spinBox.setSizePolicy(sizePolicy6)
        self.spinBox.setMinimumSize(QSize(0, 62))
        self.spinBox.setFont(font)
        self.spinBox.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.spinBox.setStyleSheet(u"")

        self.gridLayout_2.addWidget(self.spinBox, 5, 1, 1, 1)

        self.textBrowser_5 = QTextBrowser(self.page_3)
        self.textBrowser_5.setObjectName(u"textBrowser_5")
        self.textBrowser_5.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_5.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.gridLayout_2.addWidget(self.textBrowser_5, 1, 0, 1, 1)

        self.pushButton_3 = QPushButton(self.page_3)
        self.pushButton_3.setObjectName(u"pushButton_3")
        sizePolicy6.setHeightForWidth(self.pushButton_3.sizePolicy().hasHeightForWidth())
        self.pushButton_3.setSizePolicy(sizePolicy6)
        self.pushButton_3.setMinimumSize(QSize(0, 60))
        self.pushButton_3.setFont(font)

        self.gridLayout_2.addWidget(self.pushButton_3, 7, 1, 1, 1)

        self.textBrowser_9 = QTextBrowser(self.page_3)
        self.textBrowser_9.setObjectName(u"textBrowser_9")
        self.textBrowser_9.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_9.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.gridLayout_2.addWidget(self.textBrowser_9, 2, 0, 1, 1)

        self.comboBox = QComboBox(self.page_3)
        self.comboBox.addItem("")
        self.comboBox.addItem("")
        self.comboBox.addItem("")
        self.comboBox.addItem("")
        self.comboBox.addItem("")
        self.comboBox.addItem("")
        self.comboBox.addItem("")
        self.comboBox.addItem("")
        self.comboBox.addItem("")
        self.comboBox.addItem("")
        self.comboBox.addItem("")
        self.comboBox.addItem("")
        self.comboBox.addItem("")
        self.comboBox.addItem("")
        self.comboBox.addItem("")
        self.comboBox.setObjectName(u"comboBox")
        sizePolicy5.setHeightForWidth(self.comboBox.sizePolicy().hasHeightForWidth())
        self.comboBox.setSizePolicy(sizePolicy5)
        self.comboBox.setMinimumSize(QSize(0, 70))
        self.comboBox.setFont(font)
        self.comboBox.setLayoutDirection(Qt.LayoutDirection.LeftToRight)
        self.comboBox.setStyleSheet(u"QLabel { font-size: 14pt; }")

        self.gridLayout_2.addWidget(self.comboBox, 1, 1, 1, 1)

        self.comboBox_3 = QComboBox(self.page_3)
        self.comboBox_3.addItem("")
        self.comboBox_3.addItem("")
        self.comboBox_3.setObjectName(u"comboBox_3")
        sizePolicy5.setHeightForWidth(self.comboBox_3.sizePolicy().hasHeightForWidth())
        self.comboBox_3.setSizePolicy(sizePolicy5)
        self.comboBox_3.setMinimumSize(QSize(0, 70))
        self.comboBox_3.setFont(font)
        self.comboBox_3.setLayoutDirection(Qt.LayoutDirection.LeftToRight)

        self.gridLayout_2.addWidget(self.comboBox_3, 4, 1, 1, 1)

        self.comboBox_4 = QComboBox(self.page_3)
        self.comboBox_4.addItem("")
        self.comboBox_4.addItem("")
        self.comboBox_4.addItem("")
        self.comboBox_4.setObjectName(u"comboBox_4")
        sizePolicy5.setHeightForWidth(self.comboBox_4.sizePolicy().hasHeightForWidth())
        self.comboBox_4.setSizePolicy(sizePolicy5)
        self.comboBox_4.setMinimumSize(QSize(0, 70))
        self.comboBox_4.setFont(font)
        self.comboBox_4.setLayoutDirection(Qt.LayoutDirection.LeftToRight)

        self.gridLayout_2.addWidget(self.comboBox_4, 3, 1, 1, 1)

        self.textBrowser_7 = QTextBrowser(self.page_3)
        self.textBrowser_7.setObjectName(u"textBrowser_7")
        self.textBrowser_7.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_7.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.gridLayout_2.addWidget(self.textBrowser_7, 3, 0, 1, 1)

        self.textBrowser_4 = QTextBrowser(self.page_3)
        self.textBrowser_4.setObjectName(u"textBrowser_4")
        self.textBrowser_4.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_4.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.gridLayout_2.addWidget(self.textBrowser_4, 0, 0, 1, 2)

        self.textBrowser_8 = QTextBrowser(self.page_3)
        self.textBrowser_8.setObjectName(u"textBrowser_8")
        self.textBrowser_8.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_8.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.gridLayout_2.addWidget(self.textBrowser_8, 5, 0, 1, 1)

        self.textBrowser_6 = QTextBrowser(self.page_3)
        self.textBrowser_6.setObjectName(u"textBrowser_6")
        self.textBrowser_6.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_6.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.gridLayout_2.addWidget(self.textBrowser_6, 4, 0, 1, 1)

        self.pushButton_11 = QPushButton(self.page_3)
        self.pushButton_11.setObjectName(u"pushButton_11")
        sizePolicy6.setHeightForWidth(self.pushButton_11.sizePolicy().hasHeightForWidth())
        self.pushButton_11.setSizePolicy(sizePolicy6)
        self.pushButton_11.setMinimumSize(QSize(0, 60))
        self.pushButton_11.setFont(font)

        self.gridLayout_2.addWidget(self.pushButton_11, 7, 0, 1, 1)

        self.stackedWidget.addWidget(self.page_3)
        self.page_2 = QWidget()
        self.page_2.setObjectName(u"page_2")
        font2 = QFont()
        font2.setFamilies([u"Noto Sans SC"])
        font2.setBold(True)
        self.page_2.setFont(font2)
        self.page_2.setStyleSheet(u"/* ===== QComboBox: \u043f\u043e\u043b\u043d\u044b\u0439 \u0441\u0442\u0438\u043b\u044c \u0431\u0435\u0437 \u0440\u0435\u0441\u0443\u0440\u0441\u043e\u0432 ===== */\n"
"\n"
"/* --- \u043a\u043e\u043d\u0442\u0435\u0439\u043d\u0435\u0440 \u0432\u0441\u043f\u043b\u044b\u0432\u0430\u044e\u0449\u0435\u0433\u043e \u043e\u043a\u043d\u0430 (Qt-5/6) --- */\n"
"QFrame#qt_combo_box_popup {      /* << \u043a\u043b\u044e\u0447\u0435\u0432\u0430\u044f \u0441\u0442\u0440\u043e\u0447\u043a\u0430 */\n"
"    border: none;                /* \u0443\u0431\u0438\u0440\u0430\u0435\u043c \u0440\u0430\u043c\u043a\u0443 */\n"
"    background: 505050;     /* \u0438\u043b\u0438 #505050 \u043f\u043e\u0434 \u0444\u043e\u043d \u0444\u043e\u0440\u043c\u044b */\n"
"}\n"
"\n"
"\n"
"\n"
"\n"
"\n"
"\n"
"/* \u041e\u0421\u041d\u041e\u0412\u041d\u041e\u0415 \u041f\u041e\u041b\u0415 -----------------------------------------------------------*/\n"
"QComboBox {\n"
"    border: 1px solid #b4b4b4;\n"
"    border-radius: 12px;\n"
"    padding: 4px 40px 4"
                        "px 12px;   /* \u043c\u0435\u0441\u0442\u043e \u043f\u043e\u0434 \u0441\u0442\u0440\u0435\u043b\u043a\u0443 \u0441\u043f\u0440\u0430\u0432\u0430 */\n"
"    background: #f4f4f4;\n"
"    min-height: 60px;             /* \u0447\u0442\u043e\u0431\u044b \u043d\u0435 \u0441\u043f\u043b\u044e\u0449\u0438\u0432\u0430\u043b\u0441\u044f */\n"
"combobox-popup: 0;   \n"
"}\n"
"\n"
"/* \u041a\u041d\u041e\u041f\u041a\u0410 \u0412\u042b\u041f\u0410\u0414\u0410\u041d\u0418\u042f (\u043f\u0440\u0430\u0432\u044b\u0439 \u0441\u0435\u0433\u043c\u0435\u043d\u0442) --------------------------------------*/\n"
"QComboBox::drop-down {\n"
"    subcontrol-origin: padding;\n"
"    subcontrol-position: top right;\n"
"    width: 32px;\n"
"    border-left: 1px solid #b4b4b4;\n"
"    border-top-right-radius: 12px;\n"
"    border-bottom-right-radius: 12px;\n"
"    background: #e2e2e2;\n"
"}\n"
"\n"
"QComboBox::drop-down { \n"
"    background: #808080;   /* \u0432\u0440\u0435\u043c\u0435\u043d\u043d\u043e! */\n"
"}\n"
"\n"
"/* \u0421\u0422\u0420"
                        "\u0415\u041b\u041a\u0410 ----------------------------------------------------------------*/\n"
"QComboBox::down-arrow {\n"
"image: url(\":/icon/arrow_drop_down_24dp_E3E3E3_FILL0_wght400_GRAD0_opsz24.png\");\n"
"    width: 24px;      /* \u043f\u043e\u0434\u0433\u043e\u043d\u0438 \u043f\u043e\u0434 \u0440\u0435\u0430\u043b\u044c\u043d\u044b\u0439 \u0440\u0430\u0437\u043c\u0435\u0440 PNG */\n"
"    height: 24px;\n"
"    margin: 0 auto;   /* \u043f\u043e \u0446\u0435\u043d\u0442\u0440\u0443 \u043a\u043d\u043e\u043f\u043a\u0438 drop\u2011down */\n"
"    border: none;     /* \u0433\u043b\u0443\u0448\u0438\u043c \u0432\u0441\u044f\u043a\u0438\u0435 \u0441\u0442\u0430\u0440\u044b\u0435 \u0433\u0440\u0430\u043d\u0438\u0446\u044b */\n"
"}\n"
"\n"
"/* \u041f\u043e\u0432\u043e\u0440\u043e\u0442 \u043f\u0440\u0438 \u0440\u0430\u0441\u043a\u0440\u044b\u0442\u0438\u0438 --------------------------------------------------*/\n"
"QComboBox::down-arrow:on {\n"
"    transform: rotate(180deg);\n"
"}\n"
"\n"
"\n"
"\n"
"\n"
"\n"
"/* "
                        "\u0425\u041e\u0412\u0415\u0420/\u0424\u041e\u041a\u0423\u0421 -------------------------------------------------------------*/\n"
"QComboBox:hover { background: #f9f9f9; }\n"
"\n"
"QComboBox:focus {\n"
"    border: 1px solid #7aa9ff;\n"
"    outline: none;\n"
"}\n"
"\n"
"/* \u0412\u042b\u041f\u0410\u0414\u0410\u042e\u0429\u0418\u0419 \u0421\u041f\u0418\u0421\u041e\u041a -----------------------------------------------------*/\n"
"QComboBox QAbstractItemView {\n"
"    /* \u0442\u043e\u0442 \u0436\u0435 \u0440\u0430\u0434\u0438\u0443\u0441, \u0447\u0442\u043e \u0443 \u043f\u043e\u043b\u044f */\n"
"    border: 1px solid #c8c8c8;\n"
"    border-radius: 12px;\n"
"    padding: 4px;                       /* \u043b\u0451\u0433\u043a\u0438\u0439 \u00ab\u043e\u0442\u0441\u0442\u0443\u043f-\u0440\u0430\u043c\u043a\u0430\u00bb \u0432\u043d\u0443\u0442\u0440\u0438 */\n"
"    background: #FFFFFF;\n"
"\n"
"    /* \u043e\u0442\u043a\u043b\u044e\u0447\u0430\u0435\u043c \u0441\u0442\u0430\u043d\u0434\u0430\u0440\u0442\u043d\u044b"
                        "\u0439 dotted focus-rectangle */\n"
"    outline: 0;                         /* Qt >5.12 \u043f\u043e\u043d\u0438\u043c\u0430\u0435\u0442 outline */\n"
"    /* \u0435\u0441\u043b\u0438 outline \u043d\u0435 \u0440\u0430\u0431\u043e\u0442\u0430\u0435\u0442 \u0432 \u0432\u0430\u0448\u0435\u0439 \u0432\u0435\u0440\u0441\u0438\u0438:\n"
"       border: none; */\n"
"}\n"
"\n"
"\n"
"QComboBox QAbstractItemView::viewport {\n"
"    border-radius: 8px;\n"
"    background: transparent;\n"
"}\n"
"\n"
"/* \u0441\u0442\u0440\u043e\u043a\u0438 \u0432\u043d\u0443\u0442\u0440\u0438 \u0441\u043f\u0438\u0441\u043a\u0430 */\n"
"QComboBox QAbstractItemView::item {\n"
"    padding: 6px 12px;\n"
"    border-radius: 6px;                 /* \u043b\u0451\u0433\u043a\u043e\u0435 \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 hover/selected */\n"
"}\n"
"\n"
"/* \u043f\u043e\u0434\u0441\u0432\u0435\u0442\u043a\u0430 \u043d\u0430\u0432\u0435\u0434\u0435\u043d\u0438\u044f  */\n"
"QComboBox QAbstractItemView::item:hover {\n"
" "
                        "   background: #f0f0f0;\n"
"}\n"
"\n"
"/* \u0432\u044b\u0431\u0440\u0430\u043d\u043d\u044b\u0439 \u044d\u043b\u0435\u043c\u0435\u043d\u0442 (\u0431\u0435\u0437 \u043f\u0443\u043d\u043a\u0442\u0438\u0440\u0430!) */\n"
"QComboBox QAbstractItemView::item:selected {\n"
"    background: #2d97ff;                /* \u043f\u0440\u0438\u043c\u0435\u0440 \u0430\u043a\u0442\u0438\u0432\u043d\u043e\u0433\u043e \u0446\u0432\u0435\u0442\u0430 */\n"
"    color: #ffffff;\n"
"    outline: 0;                         /* \u0441\u0442\u0440\u0430\u0445\u043e\u0432\u043a\u0430 */\n"
"    /* \u0438\u043b\u0438 border: none;  -> \u0435\u0441\u043b\u0438 outline \u043d\u0435 \u043f\u043e\u0434\u0434\u0435\u0440\u0436\u0438\u0432\u0430\u0435\u0442\u0441\u044f */\n"
"}\n"
"\n"
"/* \u041e\u0444\u043e\u0440\u043c\u043b\u0435\u043d\u0438\u0435 \u0442\u0435\u043a\u0441\u0442\u0430 \u0438 \u0440\u0430\u043c\u043a\u0438 \u0434\u043b\u044f QLabel \u0438 QTextBrowser */\n"
"QLabel,\n"
"QTextBrowser {\n"
"    color: white;                    /* "
                        "\u0446\u0432\u0435\u0442 \u0448\u0440\u0438\u0444\u0442\u0430 */\n"
"    border-radius: 10px;             /* \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 \u0443\u0433\u043b\u043e\u0432 \u0440\u0430\u043c\u043a\u0438 */\n"
"    padding: 6px;                    /* \u0432\u043d\u0443\u0442\u0440\u0435\u043d\u043d\u0438\u0435 \u043e\u0442\u0441\u0442\u0443\u043f\u044b */\n"
"border: 2px solid #909090; \n"
"}\n"
"\n"
"\n"
"/* \u041d\u043e\u0440\u043c\u0430\u043b\u044c\u043d\u043e\u0435 \u0441\u043e\u0441\u0442\u043e\u044f\u043d\u0438\u0435 */\n"
"QPushButton {\n"
"    background-color: #404040;        /* \u0437\u0430\u043b\u0438\u0432\u043a\u0430 */\n"
"    color: white;                     /* \u0446\u0432\u0435\u0442 \u0442\u0435\u043a\u0441\u0442\u0430 */\n"
"    border: 2px solid #909090;        /* \u0442\u043e\u043b\u0449\u0438\u043d\u0430 \u0438 \u0446\u0432\u0435\u0442 \u043e\u0431\u0432\u043e\u0434\u043a\u0438 */\n"
"    border-radius: 12px;              /* \u0440\u0430\u0434\u0438\u0443\u0441"
                        " \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u044f */\n"
"    padding: 6px 12px;                /* \u00ab\u0432\u043e\u0437\u0434\u0443\u0445\u00bb \u0432\u043d\u0443\u0442\u0440\u0438 */\n"
"}\n"
"\n"
"/* \u041a\u0443\u0440\u0441\u043e\u0440 \u043d\u0430\u0432\u0435\u0434\u0451\u043d */\n"
"QPushButton:hover {\n"
"    background-color: #505050;\n"
"    border-color: #707070;\n"
"}\n"
"\n"
"/* \u041a\u043d\u043e\u043f\u043a\u0430 \u043d\u0430\u0436\u0430\u0442\u0430 (\u0443\u0434\u0435\u0440\u0436\u0438\u0432\u0430\u0435\u0442\u0441\u044f) */\n"
"QPushButton:pressed {\n"
"    background-color: #909090;\n"
"    border-color: #909090;\n"
"}\n"
"\n"
"/* QLabel \u0438\u043b\u0438 QTextBrowser */\n"
"QLabel, QTextBrowser {\n"
"    border: 2px solid #909090;   /* \u0442\u043e\u043b\u0449\u0438\u043d\u0430 \u0438 \u0446\u0432\u0435\u0442 */\n"
"    border-radius: 10px;         /* \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 */\n"
"    padding: 6px;                /* \u0432\u043d\u0443\u0442"
                        "\u0440\u0435\u043d\u043d\u0438\u0435 \u043e\u0442\u0441\u0442\u0443\u043f\u044b */\n"
"    color: white;              /* \u0446\u0432\u0435\u0442 \u0448\u0440\u0438\u0444\u0442\u0430 */\n"
"}\n"
"\n"
"/* ===== QSpinBox \u2014 \u0441\u0442\u0438\u043b\u044c \u043f\u043e\u0434 QComboBox (\u043a\u0430\u0436\u0434\u044b\u0439 \u043f\u0430\u0440\u0430\u043c\u0435\u0442\u0440 \u043f\u043e\u0434\u043f\u0438\u0441\u0430\u043d) ===== */\n"
"\n"
"/* \u041e\u0421\u041d\u041e\u0412\u041d\u041e\u0415 \u041f\u041e\u041b\u0415 ---------------------------------------------------------*/\n"
"QSpinBox {\n"
"    border: 1px solid #b4b4b4;                 /* \u0432\u043d\u0435\u0448\u043d\u044f\u044f \u0440\u0430\u043c\u043a\u0430 \u0432\u0438\u0434\u0436\u0435\u0442\u0430        */\n"
"    border-radius: 12px;                       /* \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 \u0432\u0441\u0435\u0445 \u0443\u0433\u043b\u043e\u0432        */\n"
"\n"
"    padding-left: 12px;                        /* \u043e\u0442"
                        "\u0441\u0442\u0443\u043f \u0442\u0435\u043a\u0441\u0442\u0430 \u0441\u043b\u0435\u0432\u0430          */\n"
"    padding-right: 40px;                       /* \u0440\u0435\u0437\u0435\u0440\u0432 \u043f\u043e\u0434 \u0431\u043b\u043e\u043a \u0441\u0442\u0440\u0435\u043b\u043e\u043a      */\n"
"    background: #f4f4f4;                       /* \u0444\u043e\u043d \u043f\u043e\u043b\u044f \u0432\u0432\u043e\u0434\u0430               */\n"
"    min-height: 60px;                          /* \u043c\u0438\u043d\u0438\u043c\u0430\u043b\u044c\u043d\u0430\u044f \u0432\u044b\u0441\u043e\u0442\u0430 \u043a\u043e\u043d\u0442\u0440\u043e\u043b\u0430  */\n"
"    color: black;                              /* \u0446\u0432\u0435\u0442 \u0432\u0432\u0435\u0434\u0451\u043d\u043d\u043e\u0433\u043e \u0442\u0435\u043a\u0441\u0442\u0430       */\n"
"\n"
"    outline: none;                             /* \u0443\u0431\u0438\u0440\u0430\u0435\u043c \u0441\u0442\u0430\u043d\u0434\u0430\u0440\u0442\u043d\u044b\u0439 \u043f\u0443\u043d\u043a"
                        "\u0442\u0438p  */\n"
"}\n"
"\n"
"/* \u0411\u041b\u041e\u041a \u0421\u0422\u0420\u0415\u041b\u041e\u041a ----------------------------------------------------------*/\n"
"/* \u043e\u0431\u0449\u0438\u0435 \u043f\u0430\u0440\u0430\u043c\u0435\u0442\u0440\u044b \u0434\u043b\u044f \u043e\u0431\u0435\u0438\u0445 \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u043e\u043a \u0431\u043b\u043e\u043a\u0430 */\n"
"QSpinBox::up-button,\n"
"QSpinBox::down-button {\n"
"    subcontrol-origin: padding;                /* \u043a\u043e\u043e\u0440\u0434\u0438\u043d\u0430\u0442\u044b \u043e\u0442 padding-box    */\n"
"    width: 32px;                               /* \u0448\u0438\u0440\u0438\u043d\u0430 \u0441\u0435\u0433\u043c\u0435\u043d\u0442\u0430 \u0441\u043e \u0441\u0442\u0440\u0435\u043b\u043a\u0430\u043c\u0438 */\n"
"    border-left: 1px solid #b4b4b4;            /* \u043b\u0438\u043d\u0438\u044f-\u0440\u0430\u0437\u0434\u0435\u043b\u0438\u0442\u0435\u043b\u044c \u0441\u043b\u0435\u0432\u0430      */\n"
"    background: #808080"
                        ";                       /* \u0444\u043e\u043d \u0431\u043b\u043e\u043a\u0430 \u0441\u0442\u0440\u0435\u043b\u043e\u043a            */\n"
"}\n"
"\n"
"/* \u2193 \u043d\u0438\u0436\u043d\u044f\u044f \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u0430 \u0431\u043b\u043e\u043a\u0430 \u0441\u0442\u0440\u0435\u043b\u043e\u043a --------------------------------------*/\n"
"QSpinBox::down-button {\n"
"    subcontrol-position: bottom right;         /* \u043f\u0440\u0438\u0432\u044f\u0437\u043a\u0430 \u043a \u043f\u0440\u0430\u0432\u043e\u043c\u0443-\u043d\u0438\u0436\u043d\u0435\u043c\u0443   */\n"
"    height: 30%;                               /* \u0437\u0430\u043d\u0438\u043c\u0430\u0435\u043c \u043e\u0441\u0442\u0430\u0432\u0448\u0438\u0435\u0441\u044f 50 %     */\n"
"    border-bottom-right-radius: 12px;          /* \u0441\u043a\u0440\u0443\u0433\u043b\u044f\u0435\u043c \u0422\u041e\u041b\u042c\u041a\u041e \u043d\u0438\u0437-\u043f\u0440\u0430\u0432.   */\n"
"}\n"
"\n"
"\n"
"/* \u2191 \u0432\u0435\u0440\u0445\u043d\u044f"
                        "\u044f \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u0430 \u0431\u043b\u043e\u043a\u0430 \u0441\u0442\u0440\u0435\u043b\u043e\u043a -------------------------------------*/\n"
"QSpinBox::up-button {\n"
"    subcontrol-position: top right;            /* \u043f\u0440\u0438\u0432\u044f\u0437\u043a\u0430 \u043a \u043f\u0440\u0430\u0432\u043e\u043c\u0443-\u0432\u0435\u0440\u0445\u043d\u0435\u043c\u0443  */\n"
"    height: 30%;                               /* \u0437\u0430\u043d\u0438\u043c\u0430\u0435\u043c \u0440\u043e\u0432\u043d\u043e \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u0443 \u0432\u044b\u0441. */\n"
"    border-top-right-radius: 12px;             /* \u0441\u043a\u0440\u0443\u0433\u043b\u044f\u0435\u043c \u0422\u041e\u041b\u042c\u041a\u041e \u0432\u0435\u0440\u0445-\u043f\u0440\u0430\u0432.  */\n"
"}\n"
"\n"
"/* \u0432\u0438\u0437\u0443\u0430\u043b\u044c\u043d\u044b\u0439 \u043e\u0442\u043a\u043b\u0438\u043a \u043f\u0440\u0438 \u043d\u0430\u0436\u0430\u0442\u0438\u0438 --------------------------------------"
                        "--*/\n"
"QSpinBox::up-button:pressed,\n"
"QSpinBox::down-button:pressed {\n"
"    background: #6d6d6d;                       /* \u0437\u0430\u0442\u0435\u043c\u043d\u044f\u0435\u043c \u0444\u043e\u043d \u043d\u0430 \u0432\u0440\u0435\u043c\u044f \u043a\u043b\u0438\u043a\u0430 */\n"
"}\n"
"\n"
"/* \u0421\u0422\u0420\u0415\u041b\u041a\u0418 (\u0438\u043a\u043e\u043d\u043a\u0438) ------------------------------------------------------*/\n"
"QSpinBox::up-arrow {\n"
"    image: url(\":/icon/arrow_drop_up_24dp_E3E3E3_FILL0_wght400_GRAD0_opsz24.png\"); /* PNG/SVG \u2193 */\n"
"    width: 24px; height: 24px;                 /* \u0433\u0430\u0431\u0430\u0440\u0438\u0442\u044b \u0438\u043a\u043e\u043d\u043a\u0438              */\n"
"    margin: 0 auto;                            /* \u0446\u0435\u043d\u0442\u0440\u0438\u0440\u0443\u0435\u043c \u0432 \u0431\u043b\u043e\u043a\u0435           */\n"
"	transform: rotate(180deg);\n"
"}\n"
"\n"
"QSpinBox::down-arrow {\n"
"    image: url(\":/icon/arrow_drop_down_24dp_E3E3E3_FILL0"
                        "_wght400_GRAD0_opsz24.png\"); /* PNG/SVG \u2193 */\n"
"    width: 24px; height: 24px;                 /* \u0433\u0430\u0431\u0430\u0440\u0438\u0442\u044b \u0438\u043a\u043e\u043d\u043a\u0438              */\n"
"    margin: 0 auto;                            /* \u0446\u0435\u043d\u0442\u0440\u0438\u0440\u0443\u0435\u043c \u0432 \u0431\u043b\u043e\u043a\u0435           */\n"
"}\n"
"\n"
"\n"
"/* \u043e\u0442\u043a\u043b\u044e\u0447\u0430\u0435\u043c \u043a\u043d\u043e\u043f\u043a\u0438 \u0438 \u0438\u043a\u043e\u043d\u043a\u0438 \u043f\u0440\u0438 \u0434\u043e\u0441\u0442\u0438\u0436\u0435\u043d\u0438\u0438 min/max ---------------------*/\n"
"QSpinBox::up-button:disabled,\n"
"QSpinBox::down-button:disabled {\n"
"    background: #c8c8c8;                       /* \u0442\u0443\u0441\u043a\u043b\u044b\u0439 \u0444\u043e\u043d \u2014 \u043a\u043d\u043e\u043f\u043a\u0430 \u043d\u0435\u0430\u043a\u0442\u0438\u0432 */\n"
"}\n"
"\n"
"QSpinBox::up-arrow:disabled,\n"
"QSpinBox::down-arrow:disabled {\n"
"    image: none;    "
                        "                           /* \u043f\u0440\u044f\u0447\u0435\u043c \u0438\u043a\u043e\u043d\u043a\u0443 \u0443 \u043d\u0435\u0430\u043a\u0442\u0438\u0432\u043d\u043e\u0439   */\n"
"}\n"
"\n"
"/* \u0425\u041e\u0412\u0415\u0420 / \u0424\u041e\u041a\u0423\u0421 ---------------------------------------------------------*/\n"
"QSpinBox:hover  { background: #f9f9f9; }       /* \u043b\u0451\u0433\u043a\u043e\u0435 \u0432\u044b\u0441\u0432\u0435\u0442\u043b\u0435\u043d\u0438\u0435 \u043f\u0440\u0438 \u0445\u043e\u0432\u0435\u0440\u0435*/\n"
"QSpinBox:focus  { border: 1px solid #7aa9ff; } /* \u0441\u0438\u043d\u044f\u044f \u0440\u0430\u043c\u043a\u0430 \u043f\u0440\u0438 \u0444\u043e\u043a\u0443\u0441\u0435       */\n"
"\n"
"/* \u041e\u0422\u041a\u041b\u042e\u0427\u0401\u041d\u041d\u041e\u0415 \u0421\u041e\u0421\u0422\u041e\u042f\u041d\u0418\u0415 -------------------------------------------------*/\n"
"QSpinBox:disabled {\n"
"    color: #8f8f8f;                            /* \u043f\u0440\u0438\u0433\u043b\u0443\u0448\u0430"
                        "\u0435\u043c \u0442\u0435\u043a\u0441\u0442             */\n"
"    background: #e0e0e0;                       /* \u0438 \u0444\u043e\u043d \u0432\u0441\u0435\u0433\u043e \u0432\u0438\u0434\u0436\u0435\u0442\u0430          */\n"
"}\n"
"\n"
"")
        self.verticalLayout_5 = QVBoxLayout(self.page_2)
        self.verticalLayout_5.setObjectName(u"verticalLayout_5")
        self.gridLayout = QGridLayout()
        self.gridLayout.setObjectName(u"gridLayout")
        self.textBrowser_2 = QTextBrowser(self.page_2)
        self.textBrowser_2.setObjectName(u"textBrowser_2")
        sizePolicy7 = QSizePolicy(QSizePolicy.Policy.Maximum, QSizePolicy.Policy.Maximum)
        sizePolicy7.setHorizontalStretch(0)
        sizePolicy7.setVerticalStretch(0)
        sizePolicy7.setHeightForWidth(self.textBrowser_2.sizePolicy().hasHeightForWidth())
        self.textBrowser_2.setSizePolicy(sizePolicy7)
        self.textBrowser_2.setMinimumSize(QSize(500, 0))
        self.textBrowser_2.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_2.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.gridLayout.addWidget(self.textBrowser_2, 0, 0, 1, 1)

        self.pushButton_5 = QPushButton(self.page_2)
        self.pushButton_5.setObjectName(u"pushButton_5")
        self.pushButton_5.setMinimumSize(QSize(0, 50))
        self.pushButton_5.setFont(font1)

        self.gridLayout.addWidget(self.pushButton_5, 1, 0, 1, 1)


        self.verticalLayout_5.addLayout(self.gridLayout)

        self.stackedWidget.addWidget(self.page_2)
        self.page_5 = QWidget()
        self.page_5.setObjectName(u"page_5")
        self.page_5.setStyleSheet(u"/* ===== QComboBox: \u043f\u043e\u043b\u043d\u044b\u0439 \u0441\u0442\u0438\u043b\u044c \u0431\u0435\u0437 \u0440\u0435\u0441\u0443\u0440\u0441\u043e\u0432 ===== */\n"
"QFrame#qt_combo_box_popup {\n"
"    background: transparent;   /* \u2190 \u0444\u043e\u043d \u043f\u043e\u043b\u043d\u043e\u0441\u0442\u044c\u044e \u201c\u0434\u044b\u0440\u044f\u0432\u044b\u0439\u201d */\n"
"    border: none;\n"
"    border-radius: 12px;\n"
"}\n"
"\n"
"\n"
"/* \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 \u0432\u0435\u0440\u0442\u0438\u043a\u0430\u043b\u044c\u043d\u044b\u0439 \u0441\u043a\u0440\u043e\u043b\u043b\u0431\u0430\u0440 \u0432\u043d\u0443\u0442\u0440\u0438 \u0432\u044b\u043f\u0430\u0434\u0430\u044e\u0449\u0435\u0433\u043e \u0441\u043f\u0438\u0441\u043a\u0430 \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500 */\n"
"QComboBox QAbstractItemView QScrollBar:vertical {\n"
"    width: 12px;               /* \u0442\u043e\u043b\u0449\u0438\u043d\u0430 \u0432\u0441\u0435\u0439 \u043f\u043e\u043b\u043e"
                        "\u0441\u044b \u043f\u0440\u043e\u043a\u0440\u0443\u0442\u043a\u0438          */\n"
"    margin: 0px 0px 0px 0;     /* \u043b\u0451\u0433\u043a\u0438\u0439 \u043e\u0442\u0441\u0442\u0443\u043f \u043e\u0442 \u043f\u0440\u0430\u0432\u043e\u0439 \u0433\u0440\u0430\u043d\u0438 \u0441\u043f\u0438\u0441\u043a\u0430   */\n"
"    background: #ffffff;   /* \u2190 \u0443\u0431\u0438\u0440\u0430\u0435\u043c \u0444\u043e\u043d \u0441\u0430\u043c\u043e\u0439 \u043f\u043e\u043b\u043e\u0441\u044b             */\n"
"    border: none;              /* \u0438 \u0440\u0430\u043c\u043a\u0443, \u043a\u043e\u0442\u043e\u0440\u0443\u044e Qt \u0440\u0438\u0441\u0443\u0435\u0442 \u043f\u043e \u0443\u043c\u043e\u043b\u0447\u0430\u043d\u0438\u044e*/\n"
"}\n"
"\n"
"/* track (\u043a\u043e\u043b\u0435\u044f). \u0414\u0435\u043b\u0430\u0435\u043c \u0435\u0451 \u043d\u0435\u0432\u0438\u0434\u0438\u043c\u043e\u0439 \u2014 \u043e\u0441\u0442\u0430\u0451\u0442\u0441\u044f \u00ab\u043f\u0443\u0441\u0442\u043e\u0435 \u043c\u0435\u0441\u0442\u043e\u00bb"
                        " */\n"
"QComboBox QAbstractItemView QScrollBar::groove:vertical {\n"
"    background: #ffffff;   /* \u043d\u0438\u043a\u0430\u043a\u043e\u0433\u043e \u0446\u0432\u0435\u0442\u0430                         */\n"
"    border: none;\n"
"    margin: 0;                 /* \u0432\u0430\u0436\u043d\u043e! \u0443\u0431\u0438\u0440\u0430\u0435\u0442 \u0432\u043d\u0443\u0442\u0440\u0435\u043d\u043d\u0438\u0435 \u00ab\u043f\u043e\u043b\u044f\u00bb Qt    */\n"
"}\n"
"\n"
"/* \u043f\u0443\u0441\u0442\u044b\u0435 \u0443\u0447\u0430\u0441\u0442\u043a\u0438 \u043d\u0430\u0434 \u0438 \u043f\u043e\u0434 \u043f\u043e\u043b\u0437\u0443\u043d\u043a\u043e\u043c \u2014 \u0442\u043e\u0436\u0435 \u0432 \u043d\u043e\u043b\u044c */\n"
"QComboBox QAbstractItemView QScrollBar::add-page:vertical,\n"
"QComboBox QAbstractItemView QScrollBar::sub-page:vertical {\n"
"    background: #ffffff;\n"
"    border: none;\n"
"}\n"
"\n"
"/* \u0441\u0430\u043c \u043f\u043e\u043b\u0437\u0443\u043d\u043e\u043a (\u00ab\u043e\u0432\u0430\u043b\u00bb) --------"
                        "-----------------------------------------*/\n"
"QComboBox QAbstractItemView QScrollBar::handle:vertical {\n"
"    background: #808080;       /* \u0446\u0432\u0435\u0442 \u00ab\u0442\u0430\u0431\u043b\u0435\u0442\u043a\u0438\u00bb                        */\n"
"    border-radius: 999px;        /* \u0441\u043a\u0440\u0443\u0433\u043b\u044f\u0435\u043c \u043a\u0440\u0430\u044f \u043f\u043e \u043f\u043e\u043b\u043d\u043e\u0439               */\n"
"    min-height: 24px;          /* \u0447\u0442\u043e\u0431\u044b \u043d\u0435 \u0438\u0441\u0447\u0435\u0437\u0430\u043b \u043f\u0440\u0438 \u043c\u0430\u043b\u0435\u043d\u044c\u043a\u043e\u043c \u043a\u043e\u043d\u0442\u0435\u043d\u0442\u0435*/\n"
"    margin: 2px;               /* \u0437\u0430\u0437\u043e\u0440 \u043e\u0442 \u0433\u0440\u0430\u043d\u0438\u0446 \u0431\u0430\u0440\u0430                   */\n"
"}\n"
"\n"
"QComboBox QAbstractItemView QScrollBar::sub-line:vertical,   /* \u0432\u0435\u0440\u0445\u043d\u044f\u044f  */\n"
"QComboBox QAbstractItemView QScrollBa"
                        "r::add-line:vertical {  /* \u043d\u0438\u0436\u043d\u044f\u044f   */\n"
"    height: 0px;                /* \u0443\u0431\u0438\u0440\u0430\u0435\u043c \u0432\u0438\u0434\u0438\u043c\u0443\u044e \u0447\u0430\u0441\u0442\u044c      */\n"
"    width:  0px;\n"
"    border: none;\n"
"    background: #ffffff;\n"
"    subcontrol-origin: margin;  /* \u0447\u0442\u043e\u0431\u044b \u043d\u0435 \u0437\u0430\u043d\u0438\u043c\u0430\u043b\u0438 \u043c\u0435\u0441\u0442\u043e    */\n"
"}\n"
"\n"
"/* \u2500\u2500 \u0435\u0441\u043b\u0438 \u0432\u0434\u0440\u0443\u0433 \u043f\u043e\u044f\u0432\u0438\u0442\u0441\u044f \u0433\u043e\u0440\u0438\u0437\u043e\u043d\u0442\u0430\u043b\u044c\u043d\u044b\u0439 \u0441\u043a\u0440\u043e\u043b\u043b\u0431\u0430\u0440 \u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500\u2500*/\n"
"QComboBox QAbstractItemView QScrollBar::sub-line:horizontal, /* \u043b\u0435\u0432\u0430\u044f    */\n"
"QComboBox QAbstractItemView QScrollBa"
                        "r::add-line:horizontal { /* \u043f\u0440\u0430\u0432\u0430\u044f  */\n"
"    width:  0px;\n"
"    height: 0px;\n"
"    border: none;\n"
"    background: #ffffff;\n"
"    subcontrol-origin: margin;\n"
"}\n"
"\n"
"/* \u041e\u0421\u041d\u041e\u0412\u041d\u041e\u0415 \u041f\u041e\u041b\u0415 -----------------------------------------------------------*/\n"
"QComboBox {\n"
"    border: 1px solid #b4b4b4;\n"
"    border-radius: 12px;\n"
"    padding: 4px 40px 4px 12px;   /* \u043c\u0435\u0441\u0442\u043e \u043f\u043e\u0434 \u0441\u0442\u0440\u0435\u043b\u043a\u0443 \u0441\u043f\u0440\u0430\u0432\u0430 */\n"
"    background: #f4f4f4;\n"
"    min-height: 60px;             /* \u0447\u0442\u043e\u0431\u044b \u043d\u0435 \u0441\u043f\u043b\u044e\u0449\u0438\u0432\u0430\u043b\u0441\u044f */\n"
"combobox-popup: 0;   \n"
"}\n"
"\n"
"/* \u041a\u041d\u041e\u041f\u041a\u0410 \u0412\u042b\u041f\u0410\u0414\u0410\u041d\u0418\u042f (\u043f\u0440\u0430\u0432\u044b\u0439 \u0441\u0435\u0433\u043c\u0435\u043d\u0442) ------------------"
                        "--------------------*/\n"
"QComboBox::drop-down {\n"
"    subcontrol-origin: padding;\n"
"    subcontrol-position: top right;\n"
"    width: 32px;\n"
"    border-left: 1px solid #b4b4b4;\n"
"    border-top-right-radius: 12px;\n"
"    border-bottom-right-radius: 12px;\n"
"    background: #e2e2e2;\n"
"}\n"
"\n"
"QComboBox::drop-down { \n"
"    background: #808080;   /* \u0432\u0440\u0435\u043c\u0435\u043d\u043d\u043e! */\n"
"}\n"
"\n"
"/* \u0421\u0422\u0420\u0415\u041b\u041a\u0410 ----------------------------------------------------------------*/\n"
"QComboBox::down-arrow {\n"
"image: url(\":/icon/arrow_drop_down_24dp_E3E3E3_FILL0_wght400_GRAD0_opsz24.png\");\n"
"    width: 24px;      /* \u043f\u043e\u0434\u0433\u043e\u043d\u0438 \u043f\u043e\u0434 \u0440\u0435\u0430\u043b\u044c\u043d\u044b\u0439 \u0440\u0430\u0437\u043c\u0435\u0440 PNG */\n"
"    height: 24px;\n"
"    margin: 0 auto;   /* \u043f\u043e \u0446\u0435\u043d\u0442\u0440\u0443 \u043a\u043d\u043e\u043f\u043a\u0438 drop\u2011down */\n"
"    border: non"
                        "e;     /* \u0433\u043b\u0443\u0448\u0438\u043c \u0432\u0441\u044f\u043a\u0438\u0435 \u0441\u0442\u0430\u0440\u044b\u0435 \u0433\u0440\u0430\u043d\u0438\u0446\u044b */\n"
"}\n"
"\n"
"/* \u041f\u043e\u0432\u043e\u0440\u043e\u0442 \u043f\u0440\u0438 \u0440\u0430\u0441\u043a\u0440\u044b\u0442\u0438\u0438 --------------------------------------------------*/\n"
"QComboBox::down-arrow:on {\n"
"    transform: rotate(180deg);\n"
"}\n"
"\n"
"\n"
"\n"
"\n"
"\n"
"/* \u0425\u041e\u0412\u0415\u0420/\u0424\u041e\u041a\u0423\u0421 -------------------------------------------------------------*/\n"
"QComboBox:hover { background: #f9f9f9; }\n"
"\n"
"QComboBox:focus {\n"
"    border: 1px solid #7aa9ff;\n"
"    outline: none;\n"
"}\n"
"\n"
"/* \u0412\u042b\u041f\u0410\u0414\u0410\u042e\u0429\u0418\u0419 \u0421\u041f\u0418\u0421\u041e\u041a -----------------------------------------------------*/\n"
"QComboBox QAbstractItemView {\n"
"    /* \u0442\u043e\u0442 \u0436\u0435 \u0440\u0430\u0434\u0438\u0443\u0441, \u0447\u0442\u043e \u0443"
                        " \u043f\u043e\u043b\u044f */\n"
"    border: 1px solid #c8c8c8;\n"
"    border-radius: 12px;\n"
"    padding: 4px;                       /* \u043b\u0451\u0433\u043a\u0438\u0439 \u00ab\u043e\u0442\u0441\u0442\u0443\u043f-\u0440\u0430\u043c\u043a\u0430\u00bb \u0432\u043d\u0443\u0442\u0440\u0438 */\n"
"    background: #FFFFFF;\n"
"\n"
"    /* \u043e\u0442\u043a\u043b\u044e\u0447\u0430\u0435\u043c \u0441\u0442\u0430\u043d\u0434\u0430\u0440\u0442\u043d\u044b\u0439 dotted focus-rectangle */\n"
"    outline: 0;                         /* Qt >5.12 \u043f\u043e\u043d\u0438\u043c\u0430\u0435\u0442 outline */\n"
"    /* \u0435\u0441\u043b\u0438 outline \u043d\u0435 \u0440\u0430\u0431\u043e\u0442\u0430\u0435\u0442 \u0432 \u0432\u0430\u0448\u0435\u0439 \u0432\u0435\u0440\u0441\u0438\u0438:\n"
"       border: none; */\n"
"}\n"
"\n"
"\n"
"QComboBox QAbstractItemView::viewport {\n"
"    border-radius: 8px;\n"
"    background: transparent;\n"
"}\n"
"\n"
"/* \u0441\u0442\u0440\u043e\u043a\u0438 \u0432\u043d\u0443\u0442\u0440\u0438"
                        " \u0441\u043f\u0438\u0441\u043a\u0430 */\n"
"QComboBox QAbstractItemView::item {\n"
"    padding: 6px 12px;\n"
"    border-radius: 6px;                 /* \u043b\u0451\u0433\u043a\u043e\u0435 \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 hover/selected */\n"
"}\n"
"\n"
"/* \u043f\u043e\u0434\u0441\u0432\u0435\u0442\u043a\u0430 \u043d\u0430\u0432\u0435\u0434\u0435\u043d\u0438\u044f  */\n"
"QComboBox QAbstractItemView::item:hover {\n"
"    background: #f0f0f0;\n"
"}\n"
"\n"
"/* \u0432\u044b\u0431\u0440\u0430\u043d\u043d\u044b\u0439 \u044d\u043b\u0435\u043c\u0435\u043d\u0442 (\u0431\u0435\u0437 \u043f\u0443\u043d\u043a\u0442\u0438\u0440\u0430!) */\n"
"QComboBox QAbstractItemView::item:selected {\n"
"    background: #2d97ff;                /* \u043f\u0440\u0438\u043c\u0435\u0440 \u0430\u043a\u0442\u0438\u0432\u043d\u043e\u0433\u043e \u0446\u0432\u0435\u0442\u0430 */\n"
"    color: #ffffff;\n"
"    outline: 0;                         /* \u0441\u0442\u0440\u0430\u0445\u043e\u0432\u043a\u0430 */\n"
"  "
                        "  /* \u0438\u043b\u0438 border: none;  -> \u0435\u0441\u043b\u0438 outline \u043d\u0435 \u043f\u043e\u0434\u0434\u0435\u0440\u0436\u0438\u0432\u0430\u0435\u0442\u0441\u044f */\n"
"}\n"
"\n"
"/* \u041e\u0444\u043e\u0440\u043c\u043b\u0435\u043d\u0438\u0435 \u0442\u0435\u043a\u0441\u0442\u0430 \u0438 \u0440\u0430\u043c\u043a\u0438 \u0434\u043b\u044f QLabel \u0438 QTextBrowser */\n"
"QLabel,\n"
"QTextBrowser {\n"
"    color: white;                    /* \u0446\u0432\u0435\u0442 \u0448\u0440\u0438\u0444\u0442\u0430 */\n"
"    border-radius: 10px;             /* \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 \u0443\u0433\u043b\u043e\u0432 \u0440\u0430\u043c\u043a\u0438 */\n"
"    padding: 6px;                    /* \u0432\u043d\u0443\u0442\u0440\u0435\u043d\u043d\u0438\u0435 \u043e\u0442\u0441\u0442\u0443\u043f\u044b */\n"
"border: 2px solid #909090; \n"
"}\n"
"\n"
"\n"
"/* \u041d\u043e\u0440\u043c\u0430\u043b\u044c\u043d\u043e\u0435 \u0441\u043e\u0441\u0442\u043e\u044f\u043d\u0438\u0435 */\n"
"QPushBu"
                        "tton {\n"
"    background-color: #404040;        /* \u0437\u0430\u043b\u0438\u0432\u043a\u0430 */\n"
"    color: white;                     /* \u0446\u0432\u0435\u0442 \u0442\u0435\u043a\u0441\u0442\u0430 */\n"
"    border: 2px solid #909090;        /* \u0442\u043e\u043b\u0449\u0438\u043d\u0430 \u0438 \u0446\u0432\u0435\u0442 \u043e\u0431\u0432\u043e\u0434\u043a\u0438 */\n"
"    border-radius: 12px;              /* \u0440\u0430\u0434\u0438\u0443\u0441 \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u044f */\n"
"    padding: 6px 12px;                /* \u00ab\u0432\u043e\u0437\u0434\u0443\u0445\u00bb \u0432\u043d\u0443\u0442\u0440\u0438 */\n"
"}\n"
"\n"
"/* \u041a\u0443\u0440\u0441\u043e\u0440 \u043d\u0430\u0432\u0435\u0434\u0451\u043d */\n"
"QPushButton:hover {\n"
"    background-color: #505050;\n"
"    border-color: #707070;\n"
"}\n"
"\n"
"/* \u041a\u043d\u043e\u043f\u043a\u0430 \u043d\u0430\u0436\u0430\u0442\u0430 (\u0443\u0434\u0435\u0440\u0436\u0438\u0432\u0430\u0435\u0442\u0441\u044f) */\n"
"QPushB"
                        "utton:pressed {\n"
"    background-color: #909090;\n"
"    border-color: #909090;\n"
"}\n"
"\n"
"/* QLabel \u0438\u043b\u0438 QTextBrowser */\n"
"QLabel, QTextBrowser {\n"
"    border: 2px solid #909090;   /* \u0442\u043e\u043b\u0449\u0438\u043d\u0430 \u0438 \u0446\u0432\u0435\u0442 */\n"
"    border-radius: 10px;         /* \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 */\n"
"    padding: 6px;                /* \u0432\u043d\u0443\u0442\u0440\u0435\u043d\u043d\u0438\u0435 \u043e\u0442\u0441\u0442\u0443\u043f\u044b */\n"
"    color: white;              /* \u0446\u0432\u0435\u0442 \u0448\u0440\u0438\u0444\u0442\u0430 */\n"
"}\n"
"\n"
"/* ===== QSpinBox \u2014 \u0441\u0442\u0438\u043b\u044c \u043f\u043e\u0434 QComboBox (\u043a\u0430\u0436\u0434\u044b\u0439 \u043f\u0430\u0440\u0430\u043c\u0435\u0442\u0440 \u043f\u043e\u0434\u043f\u0438\u0441\u0430\u043d) ===== */\n"
"\n"
"/* \u041e\u0421\u041d\u041e\u0412\u041d\u041e\u0415 \u041f\u041e\u041b\u0415 ----------------------------------------------------"
                        "-----*/\n"
"QSpinBox {\n"
"    border: 1px solid #b4b4b4;                 /* \u0432\u043d\u0435\u0448\u043d\u044f\u044f \u0440\u0430\u043c\u043a\u0430 \u0432\u0438\u0434\u0436\u0435\u0442\u0430        */\n"
"    border-radius: 12px;                       /* \u0441\u043a\u0440\u0443\u0433\u043b\u0435\u043d\u0438\u0435 \u0432\u0441\u0435\u0445 \u0443\u0433\u043b\u043e\u0432        */\n"
"\n"
"    padding-left: 12px;                        /* \u043e\u0442\u0441\u0442\u0443\u043f \u0442\u0435\u043a\u0441\u0442\u0430 \u0441\u043b\u0435\u0432\u0430          */\n"
"    padding-right: 40px;                       /* \u0440\u0435\u0437\u0435\u0440\u0432 \u043f\u043e\u0434 \u0431\u043b\u043e\u043a \u0441\u0442\u0440\u0435\u043b\u043e\u043a      */\n"
"    background: #f4f4f4;                       /* \u0444\u043e\u043d \u043f\u043e\u043b\u044f \u0432\u0432\u043e\u0434\u0430               */\n"
"    min-height: 60px;                          /* \u043c\u0438\u043d\u0438\u043c\u0430\u043b\u044c\u043d\u0430\u044f \u0432\u044b"
                        "\u0441\u043e\u0442\u0430 \u043a\u043e\u043d\u0442\u0440\u043e\u043b\u0430  */\n"
"    color: black;                              /* \u0446\u0432\u0435\u0442 \u0432\u0432\u0435\u0434\u0451\u043d\u043d\u043e\u0433\u043e \u0442\u0435\u043a\u0441\u0442\u0430       */\n"
"\n"
"    outline: none;                             /* \u0443\u0431\u0438\u0440\u0430\u0435\u043c \u0441\u0442\u0430\u043d\u0434\u0430\u0440\u0442\u043d\u044b\u0439 \u043f\u0443\u043d\u043a\u0442\u0438p  */\n"
"}\n"
"\n"
"/* \u0411\u041b\u041e\u041a \u0421\u0422\u0420\u0415\u041b\u041e\u041a ----------------------------------------------------------*/\n"
"/* \u043e\u0431\u0449\u0438\u0435 \u043f\u0430\u0440\u0430\u043c\u0435\u0442\u0440\u044b \u0434\u043b\u044f \u043e\u0431\u0435\u0438\u0445 \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u043e\u043a \u0431\u043b\u043e\u043a\u0430 */\n"
"QSpinBox::up-button,\n"
"QSpinBox::down-button {\n"
"    subcontrol-origin: padding;                /* \u043a\u043e\u043e\u0440\u0434\u0438\u043d\u0430\u0442\u044b \u043e"
                        "\u0442 padding-box    */\n"
"    width: 32px;                               /* \u0448\u0438\u0440\u0438\u043d\u0430 \u0441\u0435\u0433\u043c\u0435\u043d\u0442\u0430 \u0441\u043e \u0441\u0442\u0440\u0435\u043b\u043a\u0430\u043c\u0438 */\n"
"    border-left: 1px solid #b4b4b4;            /* \u043b\u0438\u043d\u0438\u044f-\u0440\u0430\u0437\u0434\u0435\u043b\u0438\u0442\u0435\u043b\u044c \u0441\u043b\u0435\u0432\u0430      */\n"
"    background: #808080;                       /* \u0444\u043e\u043d \u0431\u043b\u043e\u043a\u0430 \u0441\u0442\u0440\u0435\u043b\u043e\u043a            */\n"
"}\n"
"\n"
"/* \u2193 \u043d\u0438\u0436\u043d\u044f\u044f \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u0430 \u0431\u043b\u043e\u043a\u0430 \u0441\u0442\u0440\u0435\u043b\u043e\u043a --------------------------------------*/\n"
"QSpinBox::down-button {\n"
"    subcontrol-position: bottom right;         /* \u043f\u0440\u0438\u0432\u044f\u0437\u043a\u0430 \u043a \u043f\u0440\u0430\u0432\u043e\u043c\u0443-\u043d\u0438\u0436\u043d\u0435"
                        "\u043c\u0443   */\n"
"    height: 30%;                               /* \u0437\u0430\u043d\u0438\u043c\u0430\u0435\u043c \u043e\u0441\u0442\u0430\u0432\u0448\u0438\u0435\u0441\u044f 50 %     */\n"
"    border-bottom-right-radius: 12px;          /* \u0441\u043a\u0440\u0443\u0433\u043b\u044f\u0435\u043c \u0422\u041e\u041b\u042c\u041a\u041e \u043d\u0438\u0437-\u043f\u0440\u0430\u0432.   */\n"
"}\n"
"\n"
"\n"
"/* \u2191 \u0432\u0435\u0440\u0445\u043d\u044f\u044f \u043f\u043e\u043b\u043e\u0432\u0438\u043d\u0430 \u0431\u043b\u043e\u043a\u0430 \u0441\u0442\u0440\u0435\u043b\u043e\u043a -------------------------------------*/\n"
"QSpinBox::up-button {\n"
"    subcontrol-position: top right;            /* \u043f\u0440\u0438\u0432\u044f\u0437\u043a\u0430 \u043a \u043f\u0440\u0430\u0432\u043e\u043c\u0443-\u0432\u0435\u0440\u0445\u043d\u0435\u043c\u0443  */\n"
"    height: 30%;                               /* \u0437\u0430\u043d\u0438\u043c\u0430\u0435\u043c \u0440\u043e\u0432\u043d\u043e \u043f\u043e\u043b\u043e\u0432\u0438"
                        "\u043d\u0443 \u0432\u044b\u0441. */\n"
"    border-top-right-radius: 12px;             /* \u0441\u043a\u0440\u0443\u0433\u043b\u044f\u0435\u043c \u0422\u041e\u041b\u042c\u041a\u041e \u0432\u0435\u0440\u0445-\u043f\u0440\u0430\u0432.  */\n"
"}\n"
"\n"
"/* \u0432\u0438\u0437\u0443\u0430\u043b\u044c\u043d\u044b\u0439 \u043e\u0442\u043a\u043b\u0438\u043a \u043f\u0440\u0438 \u043d\u0430\u0436\u0430\u0442\u0438\u0438 ----------------------------------------*/\n"
"QSpinBox::up-button:pressed,\n"
"QSpinBox::down-button:pressed {\n"
"    background: #6d6d6d;                       /* \u0437\u0430\u0442\u0435\u043c\u043d\u044f\u0435\u043c \u0444\u043e\u043d \u043d\u0430 \u0432\u0440\u0435\u043c\u044f \u043a\u043b\u0438\u043a\u0430 */\n"
"}\n"
"\n"
"/* \u0421\u0422\u0420\u0415\u041b\u041a\u0418 (\u0438\u043a\u043e\u043d\u043a\u0438) ------------------------------------------------------*/\n"
"QSpinBox::up-arrow {\n"
"    image: url(\":/icon/arrow_drop_up_24dp_E3E3E3_FILL0_wght400_GRAD0_opsz24.png\"); /* PNG/SVG \u2193 */\n"
""
                        "    width: 24px; height: 24px;                 /* \u0433\u0430\u0431\u0430\u0440\u0438\u0442\u044b \u0438\u043a\u043e\u043d\u043a\u0438              */\n"
"    margin: 0 auto;                            /* \u0446\u0435\u043d\u0442\u0440\u0438\u0440\u0443\u0435\u043c \u0432 \u0431\u043b\u043e\u043a\u0435           */\n"
"	transform: rotate(180deg);\n"
"}\n"
"\n"
"QSpinBox::down-arrow {\n"
"    image: url(\":/icon/arrow_drop_down_24dp_E3E3E3_FILL0_wght400_GRAD0_opsz24.png\"); /* PNG/SVG \u2193 */\n"
"    width: 24px; height: 24px;                 /* \u0433\u0430\u0431\u0430\u0440\u0438\u0442\u044b \u0438\u043a\u043e\u043d\u043a\u0438              */\n"
"    margin: 0 auto;                            /* \u0446\u0435\u043d\u0442\u0440\u0438\u0440\u0443\u0435\u043c \u0432 \u0431\u043b\u043e\u043a\u0435           */\n"
"}\n"
"\n"
"\n"
"/* \u043e\u0442\u043a\u043b\u044e\u0447\u0430\u0435\u043c \u043a\u043d\u043e\u043f\u043a\u0438 \u0438 \u0438\u043a\u043e\u043d\u043a\u0438 \u043f\u0440\u0438 \u0434\u043e\u0441\u0442\u0438"
                        "\u0436\u0435\u043d\u0438\u0438 min/max ---------------------*/\n"
"QSpinBox::up-button:disabled,\n"
"QSpinBox::down-button:disabled {\n"
"    background: #c8c8c8;                       /* \u0442\u0443\u0441\u043a\u043b\u044b\u0439 \u0444\u043e\u043d \u2014 \u043a\u043d\u043e\u043f\u043a\u0430 \u043d\u0435\u0430\u043a\u0442\u0438\u0432 */\n"
"}\n"
"\n"
"QSpinBox::up-arrow:disabled,\n"
"QSpinBox::down-arrow:disabled {\n"
"    image: none;                               /* \u043f\u0440\u044f\u0447\u0435\u043c \u0438\u043a\u043e\u043d\u043a\u0443 \u0443 \u043d\u0435\u0430\u043a\u0442\u0438\u0432\u043d\u043e\u0439   */\n"
"}\n"
"\n"
"/* \u0425\u041e\u0412\u0415\u0420 / \u0424\u041e\u041a\u0423\u0421 ---------------------------------------------------------*/\n"
"QSpinBox:hover  { background: #f9f9f9; }       /* \u043b\u0451\u0433\u043a\u043e\u0435 \u0432\u044b\u0441\u0432\u0435\u0442\u043b\u0435\u043d\u0438\u0435 \u043f\u0440\u0438 \u0445\u043e\u0432\u0435\u0440\u0435*/\n"
"QSpinBox:focus  { border: 1px solid #7aa9f"
                        "f; } /* \u0441\u0438\u043d\u044f\u044f \u0440\u0430\u043c\u043a\u0430 \u043f\u0440\u0438 \u0444\u043e\u043a\u0443\u0441\u0435       */\n"
"\n"
"/* \u041e\u0422\u041a\u041b\u042e\u0427\u0401\u041d\u041d\u041e\u0415 \u0421\u041e\u0421\u0422\u041e\u042f\u041d\u0418\u0415 -------------------------------------------------*/\n"
"QSpinBox:disabled {\n"
"    color: #8f8f8f;                            /* \u043f\u0440\u0438\u0433\u043b\u0443\u0448\u0430\u0435\u043c \u0442\u0435\u043a\u0441\u0442             */\n"
"    background: #e0e0e0;                       /* \u0438 \u0444\u043e\u043d \u0432\u0441\u0435\u0433\u043e \u0432\u0438\u0434\u0436\u0435\u0442\u0430          */\n"
"}\n"
"\n"
"")
        self.gridLayout_10 = QGridLayout(self.page_5)
        self.gridLayout_10.setObjectName(u"gridLayout_10")
        self.textBrowser_3 = QTextBrowser(self.page_5)
        self.textBrowser_3.setObjectName(u"textBrowser_3")
        self.textBrowser_3.setMaximumSize(QSize(400, 200))
        self.textBrowser_3.setVerticalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)
        self.textBrowser_3.setHorizontalScrollBarPolicy(Qt.ScrollBarPolicy.ScrollBarAlwaysOff)

        self.gridLayout_10.addWidget(self.textBrowser_3, 0, 0, 1, 1)

        self.stackedWidget.addWidget(self.page_5)

        self.gridLayout_4.addWidget(self.stackedWidget, 2, 1, 1, 1)


        self.horizontalLayout_2.addWidget(self.frame)

        MainWindow.setCentralWidget(self.centralwidget)

        self.retranslateUi(MainWindow)

        self.stackedWidget.setCurrentIndex(1)
        self.stackedWidget_3.setCurrentIndex(0)
        self.stackedWidget_2.setCurrentIndex(0)
        self.stackedWidget_4.setCurrentIndex(0)


        QMetaObject.connectSlotsByName(MainWindow)
    # setupUi

    def retranslateUi(self, MainWindow):
        MainWindow.setWindowTitle(QCoreApplication.translate("MainWindow", u"URM_Configurator", None))
        self.textBrowser.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:18pt;\">\u0412\u044b\u0431\u0435\u0440\u0435\u0442\u0435 \u0441\u043f\u043e\u0441\u043e\u0431 \u043f\u043e\u0434\u043a\u043b\u044e\u0447\u0435\u043d\u0438\u044f \u0423\u0420\u041c</span></p></body></html>", None))
        self.pushButton_6.setText(QCoreApplication.translate("MainWindow", u"\u0412\u044b\u0431\u0435\u0440\u0435\u0442\u0435 COM \u043f\u043e\u0440\u0442", None))
        self.pushButton.setText(QCoreApplication.translate("MainWindow", u"\u0410\u0432\u0442\u043e\u043f\u043e\u0434\u043a\u043b\u044e\u0447\u0435\u043d\u0438\u0435", None))
        self.pushButton_2.setText(QCoreApplication.translate("MainWindow", u"\u0420\u0443\u0447\u043d\u043e\u0435 \u043f\u043e\u0434\u043a\u043b\u044e\u0447\u0435\u043d\u0438\u0435", None))
        self.textBrowser_10.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:14pt;\">\u041f\u0440\u043e\u0448\u0438\u0432\u043a\u0430 \u0437\u0430\u0433\u0440\u0443\u0436\u0435\u043d\u0430 \u0443\u0441\u043f\u0435\u0448\u043d\u043e</span></p></body></html>", None))
        self.textBrowser_11.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:14pt;\">\u041f\u0440\u043e\u0438\u0437\u043e\u0448\u043b\u0430 \u043e\u0448\u0438\u0431\u043a\u0430 \u043e\u0431\u043d\u043e\u0432\u043b\u0435\u043d\u0438\u044f</span></p></body></html>", None))
        self.pushButton_7.setText(QCoreApplication.translate("MainWindow", u"\u041e\u0431\u043d\u043e\u0432\u043b\u0435\u043d\u0438\u0435 \u041f\u041e \u0438\u0437 \u0437\u0430\u0433\u0440\u0443\u0437\u0447\u0438\u043a\u0430", None))
        self.comboBox_7.setItemText(0, QCoreApplication.translate("MainWindow", u"\u041d\u0435\u0442", None))
        self.comboBox_7.setItemText(1, QCoreApplication.translate("MainWindow", u"\u041d\u0435\u0447\u0435\u0442\u043d\u0430\u044f", None))
        self.comboBox_7.setItemText(2, QCoreApplication.translate("MainWindow", u"\u0427\u0435\u0442\u043d\u0430\u044f", None))

        self.comboBox_5.setItemText(0, QCoreApplication.translate("MainWindow", u"300", None))
        self.comboBox_5.setItemText(1, QCoreApplication.translate("MainWindow", u"600", None))
        self.comboBox_5.setItemText(2, QCoreApplication.translate("MainWindow", u"1200", None))
        self.comboBox_5.setItemText(3, QCoreApplication.translate("MainWindow", u"2400", None))
        self.comboBox_5.setItemText(4, QCoreApplication.translate("MainWindow", u"4800", None))
        self.comboBox_5.setItemText(5, QCoreApplication.translate("MainWindow", u"9600", None))
        self.comboBox_5.setItemText(6, QCoreApplication.translate("MainWindow", u"14400", None))
        self.comboBox_5.setItemText(7, QCoreApplication.translate("MainWindow", u"19200", None))
        self.comboBox_5.setItemText(8, QCoreApplication.translate("MainWindow", u"38400", None))
        self.comboBox_5.setItemText(9, QCoreApplication.translate("MainWindow", u"56000", None))
        self.comboBox_5.setItemText(10, QCoreApplication.translate("MainWindow", u"57600", None))
        self.comboBox_5.setItemText(11, QCoreApplication.translate("MainWindow", u"115200", None))
        self.comboBox_5.setItemText(12, QCoreApplication.translate("MainWindow", u"128000", None))
        self.comboBox_5.setItemText(13, QCoreApplication.translate("MainWindow", u"230400", None))
        self.comboBox_5.setItemText(14, QCoreApplication.translate("MainWindow", u"256000", None))

        self.textBrowser_74.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt;\">\u041d\u0430\u0441\u0442\u0440\u043e\u0439\u043a\u0438 USART</span></p></body></html>", None))
        self.textBrowser_66.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\">USART ID</p></body></html>", None))
        self.textBrowser_65.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\">\u0421\u0442\u043e\u043f \u0431\u0438\u0442</p></body></html>", None))
        self.textBrowser_64.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\">\u0427\u0435\u0442\u043d\u043e\u0441\u0442\u044c</p></body></html>", None))
        self.textBrowser_63.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\">\u041a\u043e\u043b\u043b\u0438\u0447\u0435\u0441\u0442\u0432\u043e \u0431\u0438\u0442</p></body></html>", None))
        self.comboBox_6.setItemText(0, QCoreApplication.translate("MainWindow", u"9", None))
        self.comboBox_6.setItemText(1, QCoreApplication.translate("MainWindow", u"8", None))

        self.textBrowser_62.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\">USART \u0441\u043a\u043e\u0440\u043e\u0441\u0442\u044c</p></body></html>", None))
        self.comboBox_8.setItemText(0, QCoreApplication.translate("MainWindow", u"1", None))
        self.comboBox_8.setItemText(1, QCoreApplication.translate("MainWindow", u"2", None))

        self.textBrowser_67.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\">Modbus timeout (\u043c\u0441)</p></body></html>", None))
        self.pushButton_13.setText(QCoreApplication.translate("MainWindow", u"\u041e\u0442\u043a\u043b\u044e\u0447\u0438\u0442\u044c", None))
        self.pushButton_4.setText(QCoreApplication.translate("MainWindow", u"\u041f\u0440\u0438\u043c\u0435\u043d\u0438\u0442\u044c \u043d\u0430\u0441\u0442\u0440\u043e\u0439\u043a\u0438", None))
        self.textBrowser_73.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\">\u041f\u0430\u0440\u043e\u043b\u044c</p></body></html>", None))
        self.OS_update.setText(QCoreApplication.translate("MainWindow", u"\u041e\u0431\u043d\u043e\u0432\u0438\u0442\u044c \u041f\u041e", None))
        self.textBrowser_83.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt;\">\u041e\u0431\u043d\u043e\u0432\u043b\u0435\u043d\u0438\u0435 \u0432\u044b\u043f\u043e\u043b\u043d\u0435\u043d\u043e \u0443\u0441\u043f\u0435\u0448\u043d\u043e, \u043d\u0435\u043e\u0431\u0445\u043e\u0434\u0438\u043c\u043e \u043f\u0435\u0440\u0435\u043f\u043e\u0434\u043a\u043b\u044e\u0447\u0435\u043d\u0438\u0435</span></p></body></html>", None))
        self.textBrowser_82.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:12pt;\">\u041e\u0448\u0438\u0431\u043a\u0430 \u043e\u0431\u043d\u043e\u0432\u043b\u0435\u043d\u0438\u044f</span></p></body></html>", None))
        self.pushButton_8.setText(QCoreApplication.translate("MainWindow", u"\u041d\u0430\u0447\u0430\u0442\u044c \u0442\u0435\u0441\u0442 \u0443\u0441\u0442\u0440\u043e\u0439\u0441\u0442\u0432\u0430", None))
        self.textBrowser_12.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:14pt;\">\u041f\u0435\u0440\u0435\u0432\u0435\u0434\u0438\u0442\u0435 \u0432\u0441\u0435 \u0442\u0443\u043c\u0431\u043b\u0435\u0440\u044b \u0432 \u043f\u043e\u043b\u043e\u0436\u0435\u043d\u0438\u0435 \u0432\u0432\u0435\u0440\u0445, \u0430 \u0442\u0430\u043a \u0436\u0435 \u0442\u0443\u043c\u0431\u043b\u0435\u0440 \u0411\u041a\u041a \u0432 \u043f\u043e\u043b\u043e"
                        "\u0436\u0435\u043d\u0438\u0435 \u0412\u041a\u041b.</span></p></body></html>", None))
        self.pushButton_12.setText(QCoreApplication.translate("MainWindow", u"\u0414\u0430\u043b\u0435\u0435", None))
        self.textBrowser_13.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:11pt;\">\u041d\u0430\u0436\u043c\u0438\u0442\u0435 \u0441\u043d\u043e\u043f\u043a\u0443 \u0441\u0442\u0430\u0440\u0442, \u0443\u0441\u0442\u0440\u043e\u0439\u0441\u0442\u0432\u043e \u0434\u043e\u043b\u0436\u043d\u043e \u043f\u043e \u043f\u043e\u0440\u044f\u0434\u043a\u0443 \u0432\u043a\u043b\u044e\u0447\u0438\u0442\u044c \u0432\u0441\u0435 \u0440\u0435\u043b"
                        "\u0435 (\u0420\u0435\u0436\u0438\u043c \u0441 \u0411\u041a\u041a)</span></p></body></html>", None))
        self.pushButton_9.setText(QCoreApplication.translate("MainWindow", u"\u0421\u0442\u0430\u0440\u0442", None))
        self.pushButton_10.setText(QCoreApplication.translate("MainWindow", u"\u0414\u0430\u043b\u0435\u0435", None))
        self.textBrowser_14.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:11pt;\">\u041f\u0435\u0440\u0435\u043a\u043b\u044e\u0447\u0438\u0442\u0435 \u0432\u0441\u0435 \u0442\u0443\u043c\u0431\u043b\u0435\u0440\u044b \u0432 \u043f\u043e\u043b\u043e\u0436\u0435\u043d\u0438\u0435 \u0432\u043d\u0438\u0437, \u0442\u0443\u043c\u0431\u043b\u0435\u0440 \u0411\u041a\u041a \u0432 \u043f\u043e\u043b\u043e\u0436\u0435\u043d\u0438\u0435 \u0432"
                        "\u044b\u043a\u043b. \u0438 \u043d\u0430\u0436\u043c\u0438\u0442\u0435 \u0434\u0430\u043b\u0435\u0435, \u0443\u0441\u0442\u0440\u043e\u0439\u0441\u0442\u0432\u043e \u0434\u043e\u043b\u0436\u043d\u043e \u043f\u043e \u043f\u043e\u0440\u044f\u0434\u043a\u0443 \u0432\u043a\u043b\u044e\u0447\u0438\u0442\u044c \u0432\u0441\u0435 \u0440\u0435\u043b\u0435. (\u0420\u0435\u0436\u0438\u043c \u0431\u0435\u0437 \u0411\u041a\u041a)</span></p></body></html>", None))
        self.pushButton_14.setText(QCoreApplication.translate("MainWindow", u"\u0421\u0442\u0430\u0440\u0442", None))
        self.pushButton_15.setText(QCoreApplication.translate("MainWindow", u"\u0414\u0430\u043b\u0435\u0435", None))
        self.comboBox_2.setItemText(0, QCoreApplication.translate("MainWindow", u"8", None))

        self.textBrowser_5.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:14pt;\">\u0421\u043a\u043e\u0440\u043e\u0441\u0442\u044c USART</span></p></body></html>", None))
        self.pushButton_3.setText(QCoreApplication.translate("MainWindow", u"\u041d\u0430\u0437\u0430\u0434", None))
        self.textBrowser_9.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:14pt;\">\u041a\u043e\u043b\u043b\u0438\u0447\u0435\u0441\u0442\u0432\u043e \u0431\u0438\u0442</span></p></body></html>", None))
        self.comboBox.setItemText(0, QCoreApplication.translate("MainWindow", u"300", None))
        self.comboBox.setItemText(1, QCoreApplication.translate("MainWindow", u"600", None))
        self.comboBox.setItemText(2, QCoreApplication.translate("MainWindow", u"1200", None))
        self.comboBox.setItemText(3, QCoreApplication.translate("MainWindow", u"2400", None))
        self.comboBox.setItemText(4, QCoreApplication.translate("MainWindow", u"4800", None))
        self.comboBox.setItemText(5, QCoreApplication.translate("MainWindow", u"9600", None))
        self.comboBox.setItemText(6, QCoreApplication.translate("MainWindow", u"14400", None))
        self.comboBox.setItemText(7, QCoreApplication.translate("MainWindow", u"19200", None))
        self.comboBox.setItemText(8, QCoreApplication.translate("MainWindow", u"38400", None))
        self.comboBox.setItemText(9, QCoreApplication.translate("MainWindow", u"56000", None))
        self.comboBox.setItemText(10, QCoreApplication.translate("MainWindow", u"57600", None))
        self.comboBox.setItemText(11, QCoreApplication.translate("MainWindow", u"115200", None))
        self.comboBox.setItemText(12, QCoreApplication.translate("MainWindow", u"128000", None))
        self.comboBox.setItemText(13, QCoreApplication.translate("MainWindow", u"230400", None))
        self.comboBox.setItemText(14, QCoreApplication.translate("MainWindow", u"256000", None))

        self.comboBox_3.setItemText(0, QCoreApplication.translate("MainWindow", u"1 \u0441\u0442\u043e\u043f \u0431\u0438\u0442", None))
        self.comboBox_3.setItemText(1, QCoreApplication.translate("MainWindow", u"2 \u0441\u0442\u043e\u043f \u0431\u0438\u0442", None))

        self.comboBox_4.setItemText(0, QCoreApplication.translate("MainWindow", u"\u043d\u0435\u0442", None))
        self.comboBox_4.setItemText(1, QCoreApplication.translate("MainWindow", u"\u041d\u0435\u0447\u0435\u0442\u043d\u0430\u044f", None))
        self.comboBox_4.setItemText(2, QCoreApplication.translate("MainWindow", u"\u0427\u0435\u0442\u043d\u0430\u044f", None))

        self.textBrowser_7.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:14pt;\">\u0427\u0435\u0442\u043d\u043e\u0441\u0442\u044c</span></p></body></html>", None))
        self.textBrowser_4.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:16pt;\">\u0420\u0443\u0447\u043d\u043e\u0435 \u043f\u043e\u0434\u043a\u043b\u044e\u0447\u0435\u043d\u0438\u0435</span></p></body></html>", None))
        self.textBrowser_8.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:14pt;\">USART ID</span></p></body></html>", None))
        self.textBrowser_6.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:14pt;\">\u0421\u0442\u043e\u043f-\u0431\u0438\u0442</span></p></body></html>", None))
        self.pushButton_11.setText(QCoreApplication.translate("MainWindow", u"\u041f\u043e\u0434\u043a\u043b\u044e\u0447\u0438\u0442\u044c\u0441\u044f", None))
        self.textBrowser_2.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:18pt;\">\u0410\u0432\u0442\u043e\u043f\u043e\u0434\u043a\u043b\u044e\u0447\u0435\u043d\u0438\u0435<br /></span><span style=\" font-size:14pt;\">\u0414\u043b\u044f \u0430\u0432\u0442\u043e\u043c\u0430\u0442\u0438\u0447\u0435\u0441\u043a\u043e\u0433\u043e \u043f\u043e\u0434\u043a\u043b\u044e\u0447\u0435\u043d\u0438\u044f \u0443\u0431\u0435\u0434\u0438\u0442\u0435"
                        "\u0441\u044c, \u0447\u0442\u043e \u0443\u0441\u0442\u0440\u043e\u0439\u0441\u0442\u0432\u043e \u0444\u0438\u0437\u0438\u0447\u0435\u0441\u043a\u0438 \u043f\u043e\u0434\u043a\u043b\u044e\u0447\u0435\u043d\u043e \u043a \u0448\u0438\u043d\u0435 RS-485, \u0430 \u0437\u0430\u0442\u0435\u043c \u043f\u0435\u0440\u0435\u0437\u0430\u043f\u0443\u0441\u0442\u0438\u0442\u0435 \u043c\u043e\u0434\u0443\u043b\u044c \u0423\u0420\u041c.</span></p></body></html>", None))
        self.pushButton_5.setText(QCoreApplication.translate("MainWindow", u"\u041d\u0430\u0437\u0430\u0434", None))
        self.textBrowser_3.setHtml(QCoreApplication.translate("MainWindow", u"<!DOCTYPE HTML PUBLIC \"-//W3C//DTD HTML 4.0//EN\" \"http://www.w3.org/TR/REC-html40/strict.dtd\">\n"
"<html><head><meta name=\"qrichtext\" content=\"1\" /><meta charset=\"utf-8\" /><style type=\"text/css\">\n"
"p, li { white-space: pre-wrap; }\n"
"hr { height: 1px; border-width: 0; }\n"
"li.unchecked::marker { content: \"\\2610\"; }\n"
"li.checked::marker { content: \"\\2612\"; }\n"
"</style></head><body style=\" font-family:'Noto Sans SC'; font-size:9pt; font-weight:400; font-style:normal;\">\n"
"<p align=\"center\" style=\" margin-top:0px; margin-bottom:0px; margin-left:0px; margin-right:0px; -qt-block-indent:0; text-indent:0px;\"><span style=\" font-size:16pt;\">\u041f\u0440\u043e\u0438\u0437\u043e\u0448\u043b\u0430 \u043e\u0448\u0438\u0431\u043a\u0430 \u0441\u043e\u0435\u0434\u0438\u043d\u0435\u043d\u0438\u044f.<br /><br />\u041f\u043e\u0436\u0430\u043b\u0443\u0439\u0441\u0442\u0430, \u043f\u0435\u0440\u0435\u043f\u043e\u0434\u043a\u043b\u044e\u0447\u0438\u0442\u0435 \u0443\u0441\u0442\u0440\u043e\u0439\u0441"
                        "\u0442\u0432\u043e</span></p></body></html>", None))
    # retranslateUi

