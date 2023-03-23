from PyQt5.QtWidgets import QWidget, QVBoxLayout, QPushButton
from lib.libbol import *
from widgets.tree_view import BolHeader

class MoreButtons(QWidget):
    def __init__(self, parent):
        super().__init__(parent)
        self.vbox = QVBoxLayout(self)
        self.vbox.setContentsMargins(0, 0, 0, 0)

    def add_buttons(self, option = None):
        self.clear_buttons()

        if option is None or isinstance(option, BolHeader):
            return

        obj = option.bound_to
        if isinstance(obj, EnemyPointGroups):
            new_enemy_group = QPushButton(self)
            new_enemy_group.setText("Add Enemy Group")
            new_enemy_group.clicked.connect(
                lambda: self.parent().parent.button_side_button_action("add_enemygroup", obj) )
            self.vbox.addWidget(new_enemy_group)
        elif isinstance(obj, EnemyPointGroup):
            new_enemy_point = QPushButton(self)
            new_enemy_point.setText("Add Enemy Points To Start")
            new_enemy_point.clicked.connect(
                lambda: self.parent().parent.button_side_button_action("add_points_start_group", obj) )
            self.vbox.addWidget(new_enemy_point)
        elif isinstance(obj, EnemyPoint):
            new_enemy_point = QPushButton(self)
            new_enemy_point.setText("Add Enemy Points Here")
            new_enemy_point.clicked.connect(
                lambda: self.parent().parent.button_side_button_action("add_points_here", obj) )
            self.vbox.addWidget(new_enemy_point)

    def clear_buttons(self):
        for i in reversed(range(self.vbox.count())):
            self.vbox.itemAt(i).widget().setParent(None)
