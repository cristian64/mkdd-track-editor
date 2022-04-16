import contextlib
import pickle
import collections
import traceback
import os
from timeit import default_timer
from copy import deepcopy
from io import TextIOWrapper, BytesIO, StringIO
from math import sin, cos, atan2, pi
import json
from PIL import Image

from PySide6 import QtCore, QtGui, QtWidgets

import opengltext
import py_obj

from lib import bti
from widgets.editor_widgets import catch_exception
from widgets.editor_widgets import AddPikObjectWindow
from widgets.tree_view import LevelDataTreeView
import widgets.tree_view as tree_view
from configuration import read_config, make_default_config, save_cfg

import mkdd_widgets # as mkddwidgets
from widgets.side_widget import PikminSideWidget
from widgets.editor_widgets import open_error_dialog, open_info_dialog, catch_exception_with_dialog
from mkdd_widgets import BolMapViewer, MODE_TOPDOWN
from lib.libbol import BOL, MGEntry, Route, get_full_name
import lib.libbol as libbol
from lib.rarc import Archive
from lib.BCOllider import RacetrackCollision
from lib.model_rendering import TexturedModel, CollisionModel, Minimap
from widgets.editor_widgets import ErrorAnalyzer, ErrorAnalyzerButton, show_minimap_generator
from lib.dolreader import DolFile, read_float, write_float, read_load_immediate_r0, write_load_immediate_r0, UnmappedAddress
from widgets.file_select import FileSelect
from lib.bmd_render import clear_temp_folder, load_textured_bmd
from lib.game_visualizer import Game
PIKMIN2GEN = "Generator files (defaultgen.txt;initgen.txt;plantsgen.txt;*.txt)"


def detect_dol_region(dol):
    try:
        dol.seek(0x803CDD38)
    except UnmappedAddress:
        pass
    else:
        if dol.read(5) == b"title":
            return "US"

    try:
        dol.seek(0x803D7B78)
    except UnmappedAddress:
        pass
    else:
        if dol.read(5) == b"title":
            return "PAL"

    try:
        dol.seek(0x803E8358)
    except UnmappedAddress:
        pass
    else:
        if dol.read(5) == b"title":
            return "JP"

    try:
        dol.seek(0x80419020)
    except UnmappedAddress:
        pass
    else:
        if dol.read(5) == b"title":
            return "US_DEBUG"


    raise RuntimeError("Unsupported DOL version/region")


def get_treeitem(root: QtWidgets.QTreeWidgetItem, obj):
    for i in range(root.childCount()):
        child = root.child(i)
        if child.bound_to == obj:
            return child
    return None


class UndoEntry:

    def __init__(self, bol_document: bytes, enemy_path_data: 'tuple[tuple[bool, int]]',
                 minimap_data: tuple):
        self.bol_document = bol_document
        self.enemy_path_data = enemy_path_data
        self.minimap_data = minimap_data

        self.bol_hash = hash((bol_document, enemy_path_data))
        self.hash = hash((self.bol_hash, self.minimap_data))

    def __eq__(self, other) -> bool:
        return self.hash == other.hash


class GenEditor(QtWidgets.QMainWindow):
    def __init__(self):
        super().__init__()
        self.level_file = BOL()

        self.undo_history: list[UndoEntry] = []
        self.redo_history: list[UndoEntry] = []
        self.undo_history_disabled_count: int  = 0

        try:
            self.configuration = read_config()
            print("Config file loaded")
        except FileNotFoundError as e:
            print("No config file found, creating default config...")
            self.configuration = make_default_config()

        self.pathsconfig = self.configuration["default paths"]
        self.editorconfig = self.configuration["editor"]
        self.current_gen_path = None

        self.setup_ui()

        self.level_view.level_file = self.level_file
        self.level_view.set_editorconfig(self.configuration["editor"])
        self.level_view.visibility_menu = self.visibility_menu

        self.collision_area_dialog = None

        self.current_coordinates = None
        self.editing_windows = {}
        self.add_object_window = AddPikObjectWindow(self)
        self.add_object_window.setWindowIcon(self.windowIcon())
        self.object_to_be_added = None

        self.edit_spawn_window = None

        self._window_title = ""
        self._user_made_change = False
        self._justupdatingselectedobject = False

        self.bco_coll = None
        self.loaded_archive = None
        self.loaded_archive_file = None
        self.next_checkpoint_start_position = None

        self._dontselectfromtree = False

        self.dolphin = Game()
        self.level_view.dolphin = self.dolphin
        self.last_chosen_type = ""

        self.first_time_3dview = True

        self.restore_geometry()

        self.undo_history.append(self.generate_undo_entry())

        self.leveldatatreeview.set_objects(self.level_file)
        self.leveldatatreeview.bound_to_group(self.level_file)

        self.setAcceptDrops(True)

    def save_geometry(self):
        if "geometry" not in self.configuration:
            self.configuration["geometry"] = {}
        geo_config = self.configuration["geometry"]

        def to_base64(byte_array: QtCore.QByteArray) -> str:
            return bytes(byte_array.toBase64()).decode(encoding='ascii')

        geo_config["window_geometry"] = to_base64(self.saveGeometry())
        geo_config["window_state"] = to_base64(self.saveState())
        geo_config["window_splitter"] = to_base64(self.horizontalLayout.saveState())

        if self.collision_area_dialog is not None:
            geo_config["collision_window_geometry"] = to_base64(
                self.collision_area_dialog.saveGeometry())

        save_cfg(self.configuration)

    def restore_geometry(self):
        if "geometry" not in self.configuration:
            return
        geo_config = self.configuration["geometry"]

        def to_byte_array(byte_array: str) -> QtCore.QByteArray:
            return QtCore.QByteArray.fromBase64(byte_array.encode(encoding='ascii'))

        if "window_geometry" in geo_config:
            self.restoreGeometry(to_byte_array(geo_config["window_geometry"]))
        if "window_state" in geo_config:
            self.restoreState(to_byte_array(geo_config["window_state"]))
        if "window_splitter" in geo_config:
            self.horizontalLayout.restoreState(to_byte_array(geo_config["window_splitter"]))

    def closeEvent(self, event: QtGui.QCloseEvent):
        self.save_geometry()

        if self._user_made_change:
            msgbox = QtWidgets.QMessageBox(self)
            size = self.fontMetrics().height() * 3
            msgbox.setIconPixmap(QtGui.QIcon('resources/warning.svg').pixmap(size, size))
            msgbox.setWindowTitle("Unsaved Changes")
            msgbox.setText('Are you sure you want to exit the application?')
            msgbox.addButton('Cancel', QtWidgets.QMessageBox.RejectRole)
            exit_button = msgbox.addButton('Exit', QtWidgets.QMessageBox.DestructiveRole)
            msgbox.exec()
            if msgbox.clickedButton() != exit_button:
                event.ignore()
                return

        super().closeEvent(event)

    @catch_exception
    def reset(self):
        self.next_checkpoint_start_position = None
        self.loaded_archive = None
        self.loaded_archive_file = None
        self.object_to_be_added = None
        self.level_view.reset(keep_collision=True)

        self.current_coordinates = None
        for key, val in self.editing_windows.items():
            val.destroy()

        self.editing_windows = {}

        if self.edit_spawn_window is not None:
            self.edit_spawn_window.destroy()
            self.edit_spawn_window = None

        self.current_gen_path = None
        self.pik_control.reset_info()
        self.pik_control.button_add_object.setChecked(False)
        #self.pik_control.button_move_object.setChecked(False)
        self._window_title = ""
        self._user_made_change = False

    def set_base_window_title(self, name):
        self._window_title = name
        if name != "":
            self.setWindowTitle("MKDD Track Editor - "+name)
        else:
            self.setWindowTitle("MKDD Track Editor")

    def set_has_unsaved_changes(self, hasunsavedchanges):
        if hasunsavedchanges and not self._user_made_change:
            self._user_made_change = True

            if self._window_title != "":
                self.setWindowTitle("MKDD Track Editor [Unsaved Changes] - " + self._window_title)
            else:
                self.setWindowTitle("MKDD Track Editor [Unsaved Changes] ")
        elif not hasunsavedchanges and self._user_made_change:
            self._user_made_change = False
            if self._window_title != "":
                self.setWindowTitle("MKDD Track Editor - " + self._window_title)
            else:
                self.setWindowTitle("MKDD Track Editor")

    def generate_undo_entry(self) -> UndoEntry:
        bol_document = self.level_file.to_bytes()

        # List containing a tuple with the emptiness and ID of each of the enemy paths.
        enemy_paths = self.level_file.enemypointgroups.groups
        enemy_path_data = tuple((not path.points, path.id) for path in enemy_paths)

        minimap = self.level_view.minimap
        minimap_data = (
            minimap.corner1.x, minimap.corner1.y, minimap.corner1.z,
            minimap.corner2.x, minimap.corner2.y, minimap.corner2.z,
            minimap.orientation
        )

        return UndoEntry(bol_document, enemy_path_data, minimap_data)

    def load_top_undo_entry(self):
        if not self.undo_history:
            return

        current_undo_entry = self.generate_undo_entry()
        undo_entry = self.undo_history[-1]

        bol_changed = current_undo_entry.bol_hash != undo_entry.bol_hash

        self.level_file = BOL.from_bytes(undo_entry.bol_document)

        # The BOL document cannot store information on empty enemy paths; this information is
        # sourced from a separate list.
        bol_enemy_paths = list(self.level_file.enemypointgroups.groups)
        self.level_file.enemypointgroups.groups.clear()
        enemy_path_data = undo_entry.enemy_path_data
        for empty, enemy_path_id in enemy_path_data:
            if empty:
                empty_enemy_path = libbol.EnemyPointGroup()
                empty_enemy_path.id = enemy_path_id
                self.level_file.enemypointgroups.groups.append(empty_enemy_path)
            else:
                enemy_path = bol_enemy_paths.pop(0)
                assert enemy_path.id == enemy_path_id
                self.level_file.enemypointgroups.groups.append(enemy_path)

        self.level_view.level_file = self.level_file
        self.leveldatatreeview.set_objects(self.level_file)

        minimap = self.level_view.minimap
        minimap.corner1.x = undo_entry.minimap_data[0]
        minimap.corner1.y = undo_entry.minimap_data[1]
        minimap.corner1.z = undo_entry.minimap_data[2]
        minimap.corner2.x = undo_entry.minimap_data[3]
        minimap.corner2.y = undo_entry.minimap_data[4]
        minimap.corner2.z = undo_entry.minimap_data[5]
        minimap.orientation = undo_entry.minimap_data[6]

        self.update_3d()
        self.pik_control.update_info()

        if bol_changed:
            self.set_has_unsaved_changes(True)
            self.error_analyzer_button.analyze_bol(self.level_file)

    def on_undo_action_triggered(self):
        if len(self.undo_history) > 1:
            self.redo_history.insert(0, self.undo_history.pop())
            self.update_undo_redo_actions()
            self.load_top_undo_entry()

    def on_redo_action_triggered(self):
        if self.redo_history:
            self.undo_history.append(self.redo_history.pop(0))
            self.update_undo_redo_actions()
            self.load_top_undo_entry()

    def on_document_potentially_changed(self, update_unsaved_changes=True):
        # Early out if undo history is temporarily disabled.
        if self.undo_history_disabled_count:
            return

        undo_entry = self.generate_undo_entry()

        if self.undo_history[-1] != undo_entry:
            bol_changed = self.undo_history[-1].bol_hash != undo_entry.bol_hash

            self.undo_history.append(undo_entry)
            self.redo_history.clear()
            self.update_undo_redo_actions()

            if bol_changed:
                if update_unsaved_changes:
                    self.set_has_unsaved_changes(True)

                self.error_analyzer_button.analyze_bol(self.level_file)

    def update_undo_redo_actions(self):
        self.undo_action.setEnabled(len(self.undo_history) > 1)
        self.redo_action.setEnabled(bool(self.redo_history))

    @contextlib.contextmanager
    def undo_history_disabled(self):
        self.undo_history_disabled_count += 1
        try:
            yield
        finally:
            self.undo_history_disabled_count -= 1

        self.on_document_potentially_changed()

    @catch_exception_with_dialog
    def do_goto_action(self, item, index):
        _ = index
        self.tree_select_object(item)
        self.frame_selection(adjust_zoom=False)

    def frame_selection(self, adjust_zoom):
        selected_only = bool(self.level_view.selected_positions)
        minx, miny, minz, maxx, maxy, maxz = self.compute_objects_extent(selected_only)

        # Center of the extent.
        x = (maxx + minx) / 2
        y = (maxy + miny) / 2
        z = (maxz + minz) / 2

        if self.level_view.mode == MODE_TOPDOWN:
            self.level_view.offset_z = -z
            self.level_view.offset_x = -x

            if adjust_zoom:
                if self.level_view.canvas_width > 0 and self.level_view.canvas_height > 0:
                    MARGIN = 2000
                    deltax = maxx - minx + MARGIN
                    deltay = maxz - minz + MARGIN
                    hzoom = deltax / self.level_view.canvas_width * 10
                    vzoom = deltay / self.level_view.canvas_height * 10
                    DEFAULT_ZOOM = 80
                    self.level_view._zoom_factor = max(hzoom, vzoom, DEFAULT_ZOOM)
        else:
            look = self.level_view.camera_direction.copy()

            if adjust_zoom:
                MARGIN = 3000
                deltax = maxx - minx + MARGIN
                fac = deltax
            else:
                fac = 5000

            self.level_view.offset_z = -(z + look.y * fac)
            self.level_view.offset_x = x - look.x * fac
            self.level_view.camera_height = y - look.z * fac

        self.level_view.do_redraw()

    def compute_objects_extent(self, selected_only):
        extent = []

        def extend(position):
            if not extent:
                extent.extend([position.x, position.y, position.z,
                               position.x, position.y, position.z])
                return

            extent[0] = min(extent[0], position.x)
            extent[1] = min(extent[1], position.y)
            extent[2] = min(extent[2], position.z)
            extent[3] = max(extent[3], position.x)
            extent[4] = max(extent[4], position.y)
            extent[5] = max(extent[5], position.z)

        if selected_only:
            for selected_position in self.level_view.selected_positions:
                extend(selected_position)
            return tuple(extent) or (0, 0, 0, 0, 0, 0)

        if self.visibility_menu.enemyroute.is_visible():
            for enemy_path in self.level_file.enemypointgroups.groups:
                for enemy_path_point in enemy_path.points:
                    extend(enemy_path_point.position)

        visible_objectroutes = self.visibility_menu.objectroutes.is_visible()
        visible_cameraroutes = self.visibility_menu.cameraroutes.is_visible()
        visible_unassignedroutes = self.visibility_menu.unassignedroutes.is_visible()

        if visible_objectroutes or visible_cameraroutes or visible_unassignedroutes:
            camera_routes = set(camera.route for camera in self.level_file.cameras)
            object_routes = set(obj.pathid for obj in self.level_file.objects.objects)
            assigned_routes = camera_routes.union(object_routes)

            for i, object_route in enumerate(self.level_file.routes):
                if (not ((i in object_routes and visible_objectroutes) or
                         (i in camera_routes and visible_cameraroutes) or
                         (i not in assigned_routes and visible_unassignedroutes))):
                    continue
                for object_route_point in object_route.points:
                    extend(object_route_point.position)

        if self.visibility_menu.checkpoints.is_visible():
            for checkpoint_group in self.level_file.checkpoints.groups:
                for checkpoint in checkpoint_group.points:
                    extend(checkpoint.start)
                    extend(checkpoint.end)
        if self.visibility_menu.objects.is_visible():
            for object_ in self.level_file.objects.objects:
                extend(object_.position)
        if self.visibility_menu.areas.is_visible():
            for area in self.level_file.areas.areas:
                extend(area.position)
        if self.visibility_menu.cameras.is_visible():
            for camera in self.level_file.cameras:
                extend(camera.position)
        if self.visibility_menu.respawnpoints.is_visible():
            for respawn_point in self.level_file.respawnpoints:
                extend(respawn_point.position)
        if self.visibility_menu.kartstartpoints.is_visible():
            for karts_point in self.level_file.kartpoints.positions:
                extend(karts_point.position)
        if (self.level_view.minimap is not None and self.level_view.minimap.is_available()
                and self.visibility_menu.minimap.is_visible()):
            extend(self.level_view.minimap.corner1)
            extend(self.level_view.minimap.corner2)

        if self.level_view.collision is not None and self.level_view.collision.verts:
            vertices = self.level_view.collision.verts
            min_x = min(x for x, _y, _z in vertices)
            min_y = min(y for _x, y, _z in vertices)
            min_z = min(z for _x, _y, z in vertices)
            max_x = max(x for x, _y, _z in vertices)
            max_y = max(y for _x, y, _z in vertices)
            max_z = max(z for _x, _y, z in vertices)

            if extent:
                extent[0] = min(extent[0], min_x)
                extent[1] = min(extent[1], min_y)
                extent[2] = min(extent[2], min_z)
                extent[3] = max(extent[3], max_x)
                extent[4] = max(extent[4], max_y)
                extent[5] = max(extent[5], max_z)
            else:
                extent.extend([min_x, min_y, min_z, max_x, max_y, max_z])

        return tuple(extent) or (0, 0, 0, 0, 0, 0)

    def tree_select_arrowkey(self):
        current = self.leveldatatreeview.selectedItems()
        if len(current) == 1:
            self.tree_select_object(current[0])

    def tree_select_object(self, item):
        """if self._dontselectfromtree:
            #print("hmm")
            #self._dontselectfromtree = False
            return"""

        print("Selected:", item)
        self.level_view.selected = []
        self.level_view.selected_positions = []
        self.level_view.selected_rotations = []

        if isinstance(item, (tree_view.CameraEntry, tree_view.RespawnEntry, tree_view.AreaEntry, tree_view.ObjectEntry,
                             tree_view.KartpointEntry, tree_view.EnemyRoutePoint, tree_view.ObjectRoutePoint)):
            bound_to = item.bound_to
            self.level_view.selected = [bound_to]
            self.level_view.selected_positions = [bound_to.position]

            if hasattr(bound_to, "rotation"):
                self.level_view.selected_rotations = [bound_to.rotation]

        elif isinstance(item, tree_view.Checkpoint):
            bound_to = item.bound_to
            self.level_view.selected = [bound_to]
            self.level_view.selected_positions = [bound_to.start, bound_to.end]
        elif isinstance(item, (tree_view.EnemyPointGroup, tree_view.CheckpointGroup, tree_view.ObjectPointGroup)):
            self.level_view.selected = [item.bound_to]
        elif isinstance(item, tree_view.BolHeader) and self.level_file is not None:
            self.level_view.selected = [self.level_file]
        elif isinstance(item, (tree_view.LightParamEntry, tree_view.MGEntry)):
            self.level_view.selected = [item.bound_to]

        self.pik_control.set_buttons(item)

        self.level_view.gizmo.move_to_average(self.level_view.selected_positions,
                                              self.level_view.selected_rotations)
        self.level_view.do_redraw()
        self.level_view.select_update.emit()

    def setup_ui(self):
        self.resize(1000, 800)
        self.set_base_window_title("")

        self.setup_ui_menubar()
        self.setup_ui_toolbar()

        #self.centralwidget = QWidget(self)
        #self.centralwidget.setObjectName("centralwidget")

        self.horizontalLayout = QtWidgets.QSplitter()
        self.centralwidget = self.horizontalLayout
        self.setCentralWidget(self.horizontalLayout)
        self.leveldatatreeview = LevelDataTreeView(self.centralwidget)
        #self.leveldatatreeview.itemClicked.connect(self.tree_select_object)
        self.leveldatatreeview.itemDoubleClicked.connect(self.do_goto_action)
        self.leveldatatreeview.itemSelectionChanged.connect(self.tree_select_arrowkey)

        self.level_view = BolMapViewer(int(self.editorconfig.get("multisampling", 8)),
                                       self.centralwidget)
        self.level_view.editor = self

        self.horizontalLayout.setObjectName("horizontalLayout")
        self.horizontalLayout.addWidget(self.leveldatatreeview)
        self.horizontalLayout.addWidget(self.level_view)
        self.leveldatatreeview.resize(200, self.leveldatatreeview.height())

        self.pik_control = PikminSideWidget(self)
        self.horizontalLayout.addWidget(self.pik_control)

        QtGui.QShortcut(QtGui.QKeySequence(QtCore.Qt.Key_G), self).activated.connect(self.action_ground_objects)
        #QtGui.QShortcut(QtCore.Qt.CTRL + QtCore.Qt.Key_A, self).activated.connect(self.shortcut_open_add_item_window)
        self.statusbar = QtWidgets.QStatusBar(self)
        self.statusbar.setObjectName("statusbar")
        self.setStatusBar(self.statusbar)

        self.error_analyzer_button = ErrorAnalyzerButton()
        self.error_analyzer_button.clicked.connect(lambda _checked: self.analyze_for_mistakes())
        self.statusbar.addPermanentWidget(self.error_analyzer_button)

        self.connect_actions()

    @catch_exception_with_dialog
    def setup_ui_menubar(self):
        self.menubar = QtWidgets.QMenuBar(self)
        self.file_menu = QtWidgets.QMenu(self)
        self.file_menu.setTitle("File")

        save_file_shortcut = QtGui.QShortcut(QtCore.Qt.CTRL | QtCore.Qt.Key_S, self.file_menu)
        save_file_shortcut.activated.connect(self.button_save_level)
        #QtGui.QShortcut(QtCore.Qt.CTRL + QtCore.Qt.Key_O, self.file_menu).activated.connect(self.button_load_level)
        #QtGui.QShortcut(QtCore.Qt.CTRL + QtCore.Qt.Key_Alt + QtCore.Qt.Key_S, self.file_menu).activated.connect(self.button_save_level_as)

        self.file_load_action = QtGui.QAction("Load", self)
        self.file_load_recent_menu = QtWidgets.QMenu("Load Recent", self)
        self.save_file_action = QtGui.QAction("Save", self)
        self.save_file_as_action = QtGui.QAction("Save As", self)
        self.save_file_action.setShortcut("Ctrl+S")
        self.file_load_action.setShortcut("Ctrl+O")
        self.save_file_as_action.setShortcut("Ctrl+Alt+S")

        self.save_file_copy_as_action = QtGui.QAction("Save Copy As", self)

        self.file_load_action.triggered.connect(self.button_load_level)
        self.save_file_action.triggered.connect(self.button_save_level)
        self.save_file_as_action.triggered.connect(self.button_save_level_as)
        self.save_file_copy_as_action.triggered.connect(self.button_save_level_copy_as)


        self.file_menu.addAction(self.file_load_action)
        self.file_menu.addMenu(self.file_load_recent_menu)
        self.file_menu.addSeparator()
        self.file_menu.addAction(self.save_file_action)
        self.file_menu.addAction(self.save_file_as_action)
        self.file_menu.addAction(self.save_file_copy_as_action)

        self.file_menu.aboutToShow.connect(self.on_file_menu_aboutToShow)

        self.edit_menu = QtWidgets.QMenu(self)
        self.edit_menu.setTitle("Edit")
        self.undo_action = self.edit_menu.addAction('Undo')
        self.undo_action.setShortcut(QtGui.QKeySequence('Ctrl+Z'))
        self.undo_action.triggered.connect(self.on_undo_action_triggered)
        self.redo_action = self.edit_menu.addAction('Redo')
        self.redo_action.setShortcuts([
            QtGui.QKeySequence('Ctrl+Shift+Z'),
            QtGui.QKeySequence('Ctrl+Y'),
        ])
        self.redo_action.triggered.connect(self.on_redo_action_triggered)
        self.update_undo_redo_actions()

        self.edit_menu.addSeparator()
        self.cut_action = self.edit_menu.addAction("Cut")
        self.cut_action.setShortcut(QtGui.QKeySequence('Ctrl+X'))
        self.cut_action.triggered.connect(self.on_cut_action_triggered)
        self.copy_action = self.edit_menu.addAction("Copy")
        self.copy_action.setShortcut(QtGui.QKeySequence('Ctrl+C'))
        self.copy_action.triggered.connect(self.on_copy_action_triggered)
        self.paste_action = self.edit_menu.addAction("Paste")
        self.paste_action.setShortcut(QtGui.QKeySequence('Ctrl+V'))
        self.paste_action.triggered.connect(self.on_paste_action_triggered)

        self.visibility_menu = mkdd_widgets.FilterViewMenu(self)
        self.visibility_menu.filter_update.connect(self.on_filter_update)
        filters = self.editorconfig["filter_view"].split(",")
        for object_toggle in self.visibility_menu.get_entries():
            if object_toggle.action_view_toggle.text() in filters:
                object_toggle.action_view_toggle.blockSignals(True)
                object_toggle.action_view_toggle.setChecked(False)
                object_toggle.action_view_toggle.blockSignals(False)
            if object_toggle.action_select_toggle.text() in filters:
                object_toggle.action_select_toggle.blockSignals(True)
                object_toggle.action_select_toggle.setChecked(False)
                object_toggle.action_select_toggle.blockSignals(False)

        # ------ Collision Menu
        self.collision_menu = QtWidgets.QMenu(self.menubar)
        self.collision_menu.setTitle("Geometry")
        self.collision_load_action = QtGui.QAction("Load OBJ", self)
        self.collision_load_action.triggered.connect(self.button_load_collision)
        self.collision_menu.addAction(self.collision_load_action)
        self.collision_load_grid_action = QtGui.QAction("Load BCO", self)
        self.collision_load_grid_action.triggered.connect(self.button_load_collision_bco)
        self.collision_menu.addAction(self.collision_load_grid_action)
        self.collision_load_bmd_action = QtGui.QAction("Load BMD", self)
        self.collision_load_bmd_action.triggered.connect(self.button_load_collision_bmd)
        self.collision_menu.addAction(self.collision_load_bmd_action)
        self.collision_menu.addSeparator()
        cull_faces_action = self.collision_menu.addAction("Cull Faces")
        cull_faces_action.setCheckable(True)
        cull_faces_action.setChecked(self.editorconfig.get("cull_faces") == "True")
        cull_faces_action.triggered.connect(self.on_cull_faces_triggered)
        self.collision_menu.addSeparator()
        self.choose_default_collision = QtWidgets.QMenu("Choose Autoloaded Geometry", self)
        self.collision_menu.addMenu(self.choose_default_collision)
        self.auto_load_choose = self.choose_default_collision.addAction("Always Ask")
        self.auto_load_choose.setCheckable(True)
        self.auto_load_choose.setChecked(self.editorconfig.get("addi_file_on_load") == "Choose")
        self.auto_load_choose.triggered.connect(lambda: self.on_default_geometry_changed("Choose"))
        self.auto_load_bco = self.choose_default_collision.addAction("BCO")
        self.auto_load_bco.setCheckable(True)
        self.auto_load_bco.setChecked(self.editorconfig.get("addi_file_on_load") == "BCO")
        self.auto_load_bco.triggered.connect(lambda: self.on_default_geometry_changed("BCO"))
        self.auto_load_bmd = self.choose_default_collision.addAction("BMD")
        self.auto_load_bmd.setCheckable(True)
        self.auto_load_bmd.setChecked(self.editorconfig.get("addi_file_on_load") == "BMD")
        self.auto_load_bmd.triggered.connect(lambda: self.on_default_geometry_changed("BMD"))
        self.auto_load_none = self.choose_default_collision.addAction("Nothing")
        self.auto_load_none.setCheckable(True)
        self.auto_load_none.setChecked(self.editorconfig.get("addi_file_on_load") == "None")
        self.auto_load_none.triggered.connect(lambda: self.on_default_geometry_changed("None"))
        if self.editorconfig.get("addi_file_on_load") not in ("BCO", "BMD", "None", "Choose"):
            self.on_default_geometry_changed("Choose")
        self.collision_menu.addSeparator()
        self.clear_current_collision = QtGui.QAction("Clear Current Model", self)
        self.clear_current_collision.triggered.connect(self.clear_collision)
        self.collision_menu.addAction(self.clear_current_collision)

        self.minimap_menu = QtWidgets.QMenu(self.menubar)
        self.minimap_menu.setTitle("Minimap")
        load_minimap = QtGui.QAction("Load Minimap Image", self)
        save_minimap_png = QtGui.QAction("Save Minimap Image as PNG", self)
        save_minimap_bti = QtGui.QAction("Save Minimap Image as BTI", self)
        load_coordinates_dol = QtGui.QAction("Load Data from DOL", self)
        save_coordinates_dol = QtGui.QAction("Save Data to DOL", self)
        load_coordinates_json = QtGui.QAction("Load Data from JSON", self)
        save_coordinates_json = QtGui.QAction("Save Data to JSON", self)
        minimap_generator_action = QtGui.QAction("Minimap Generator", self)
        minimap_generator_action.setShortcut("Ctrl+M")


        load_minimap.triggered.connect(self.action_load_minimap_image)
        save_minimap_png.triggered.connect(
            lambda checked: self.action_save_minimap_image(checked, 'png'))
        save_minimap_bti.triggered.connect(
            lambda checked: self.action_save_minimap_image(checked, 'bti'))
        load_coordinates_dol.triggered.connect(self.action_load_dol)
        save_coordinates_dol.triggered.connect(self.action_save_to_dol)
        load_coordinates_json.triggered.connect(self.action_load_coordinates_json)
        save_coordinates_json.triggered.connect(self.action_save_coordinates_json)
        minimap_generator_action.triggered.connect(self.minimap_generator_action)
        self.minimap_menu.addAction(load_minimap)
        self.minimap_menu.addAction(save_minimap_png)
        self.minimap_menu.addAction(save_minimap_bti)
        self.minimap_menu.addSeparator()
        self.minimap_menu.addAction(load_coordinates_dol)
        self.minimap_menu.addAction(save_coordinates_dol)
        self.minimap_menu.addAction(load_coordinates_json)
        self.minimap_menu.addAction(save_coordinates_json)
        self.minimap_menu.addSeparator()
        self.minimap_menu.addAction(minimap_generator_action)

        # Misc
        self.misc_menu = QtWidgets.QMenu(self.menubar)
        self.misc_menu.setTitle("Misc")
        #self.spawnpoint_action = QtGui.QAction("Set startPos/Dir", self)
        #self.spawnpoint_action.triggered.connect(self.action_open_rotationedit_window)
        #self.misc_menu.addAction(self.spawnpoint_action)
        self.rotation_mode = QtGui.QAction("Rotate Positions around Pivot", self)
        self.rotation_mode.setCheckable(True)
        self.rotation_mode.setChecked(True)
        self.frame_action = QtGui.QAction("Frame Selection/All", self)
        self.frame_action.triggered.connect(
            lambda _checked: self.frame_selection(adjust_zoom=True))
        self.frame_action.setShortcut("F")
        self.misc_menu.addAction(self.rotation_mode)
        self.misc_menu.addAction(self.frame_action)
        self.analyze_action = QtGui.QAction("Analyze for common mistakes", self)
        self.analyze_action.triggered.connect(self.analyze_for_mistakes)
        self.misc_menu.addAction(self.analyze_action)

        self.misc_menu.aboutToShow.connect(
            lambda: self.frame_action.setText(
                "Frame Selection" if self.level_view.selected_positions else "Frame All"))

        self.view_action_group = QtGui.QActionGroup(self)

        self.change_to_topdownview_action = QtGui.QAction("Topdown View", self)
        self.view_action_group.addAction(self.change_to_topdownview_action)
        self.change_to_topdownview_action.triggered.connect(self.change_to_topdownview)
        self.misc_menu.addAction(self.change_to_topdownview_action)
        self.change_to_topdownview_action.setCheckable(True)
        self.change_to_topdownview_action.setChecked(True)
        self.change_to_topdownview_action.setShortcut("Ctrl+1")

        self.change_to_3dview_action = QtGui.QAction("3D View", self)
        self.view_action_group.addAction(self.change_to_3dview_action)
        self.change_to_3dview_action.triggered.connect(self.change_to_3dview)
        self.misc_menu.addAction(self.change_to_3dview_action)
        self.change_to_3dview_action.setCheckable(True)
        self.change_to_3dview_action.setShortcut("Ctrl+2")

        self.choose_bco_area = QtGui.QAction("Collision Areas (BCO)")
        self.choose_bco_area.triggered.connect(self.action_choose_bco_area)
        self.misc_menu.addAction(self.choose_bco_area)
        self.choose_bco_area.setShortcut("Ctrl+3")

        self.menubar.addAction(self.file_menu.menuAction())
        self.menubar.addAction(self.edit_menu.menuAction())
        self.menubar.addAction(self.visibility_menu.menuAction())
        self.menubar.addAction(self.collision_menu.menuAction())
        self.menubar.addAction(self.minimap_menu.menuAction())
        self.menubar.addAction(self.misc_menu.menuAction())
        self.setMenuBar(self.menubar)

        self.last_obj_select_pos = 0


        self.dolphin_action = QtGui.QAction("Hook into Dolphin", self)
        self.dolphin_action.triggered.connect(self.action_hook_into_dolphion)
        self.misc_menu.addAction(self.dolphin_action)

        self.camera_actions = [QtGui.QAction("Unfollow", self)]

        for i in range(8):
            self.camera_actions.append(QtGui.QAction("Follow Player {0}".format(i+1)))

        def make_func(i):
            def action_follow_player():
                print("Now Following", i)
                self.dolphin.stay_focused_on_player = i
            return action_follow_player

        for i in range(-1, 8):
            action = self.camera_actions[i+1]
            action.triggered.connect(make_func(i))

            self.misc_menu.addAction(action)

        reverse_official_track_action = self.misc_menu.addAction("Reverse Official Track")
        reverse_official_track_action.setShortcut("Ctrl+`")
        reverse_official_track_action.triggered.connect(self.action_reverse_official_track)

        def copy_position():
            lines = []
            for position in self.level_view.selected_positions:
                line = f'{int(position.x)}, {int(position.y)}, {int(position.z)}'
                lines.append(line)
            QtWidgets.QApplication.clipboard().setText('\n'.join(lines))
            print(f'Clipboard changed: {"  ".join(lines)}')

        copy_position_action = self.misc_menu.addAction("Copy Position")
        copy_position_action.setShortcut("Ctrl+Shift+P")
        copy_position_action.triggered.connect(copy_position)

    def action_hook_into_dolphion(self):
        error = self.dolphin.initialize()
        if error != "":
            open_error_dialog(error, self)

    def action_load_minimap_image(self):
        supported_extensions = [f'*{ext}' for ext in Image.registered_extensions()]
        supported_extensions.insert(0, '*.bti')
        supported_extensions = ' '.join(supported_extensions)

        if "minimap_image" not in self.pathsconfig:
            self.pathsconfig["minimap_image"] = ""

        filepath, choosentype = QtWidgets.QFileDialog.getOpenFileName(
            self, "Open Image", self.pathsconfig["minimap_image"],
            f"Images ({supported_extensions});;All files (*)")

        if filepath:
            if filepath.endswith('.bti'):
                with open(filepath, 'rb') as f:
                    bti_image = bti.BTI(f)
                    self.level_view.minimap.set_texture(bti_image.render())
            else:
                self.level_view.minimap.set_texture(filepath)
            self.level_view.do_redraw()

            self.pathsconfig["minimap_image"] = filepath
            save_cfg(self.configuration)

    def action_save_minimap_image(self, checked: bool = False, extension: str = 'png'):
        if not self.level_view.minimap.has_texture():
            open_info_dialog('No minimap image has been loaded yet.', self)
            return

        if "minimap_image" not in self.pathsconfig:
            self.pathsconfig["minimap_image"] = ""

        initial_filepath = self.pathsconfig["minimap_image"]
        stem, _ext = os.path.splitext(initial_filepath)
        initial_filepath = f'{stem}.{extension}'

        filepath, _choosentype = QtWidgets.QFileDialog.getSaveFileName(
            self, f"Save {extension.upper()} Image", initial_filepath,
            f"{extension.upper()} (*.{extension})")

        if filepath:
            image = self.level_view.minimap.get_texture().convert('RGBA')
            if extension == 'bti':
                for pixel in image.getdata():
                    if pixel[0] != pixel[1] or pixel[0] != pixel[2]:
                        colorful = True
                        break
                else:
                    colorful = False
                image_format = bti.ImageFormat.RGB5A3 if colorful else bti.ImageFormat.IA4
                bti_image = bti.BTI.create_from_image(image, image_format)
                bti_image.save(filepath)
            else:
                image.save(filepath)

            self.pathsconfig["minimap_image"] = filepath
            save_cfg(self.configuration)

    @catch_exception_with_dialog
    def action_load_dol(self):
        filepath, choosentype = QtWidgets.QFileDialog.getOpenFileName(
            self, "Open File",
            self.pathsconfig["dol"],
            "Game Executable (*.dol);;All files (*)")

        if filepath:
            with open("lib/minimap_locations.json", "r") as f:
                addresses_json = json.load(f)

            with open(filepath, "rb") as f:
                dol = DolFile(f)
                region = detect_dol_region(dol)

            addresses = addresses_json[region]

            item_list = ["None"]
            item_list.extend(addresses.keys())
            result, pos = FileSelect.open_file_list(self, item_list, "Select Track Slot")

            if result == "None" or result is None:
                return

            corner1x, corner1z, corner2x, corner2z, orientation = addresses[result]
            with open(filepath, "rb") as f:
                dol = DolFile(f)

                dol.seek(int(orientation, 16))
                orientation = read_load_immediate_r0(dol)
                if orientation not in (0, 1, 2, 3):
                    raise RuntimeError("Wrong Address, orientation value in DOL isn't in 0-3 range: {0}. Maybe you are using"
                                       " a dol from a different version?".format(orientation))
                self.level_view.minimap.orientation = orientation
                dol.seek(int(corner1x, 16))
                self.level_view.minimap.corner1.x = read_float(dol)
                dol.seek(int(corner1z, 16))
                self.level_view.minimap.corner1.z = read_float(dol)
                dol.seek(int(corner2x, 16))
                self.level_view.minimap.corner2.x = read_float(dol)
                dol.seek(int(corner2z, 16))
                self.level_view.minimap.corner2.z = read_float(dol)
                self.level_view.do_redraw()

            self.pathsconfig["dol"] = filepath
            save_cfg(self.configuration)

    @catch_exception_with_dialog
    def action_save_to_dol(self, val):
        filepath, choosentype = QtWidgets.QFileDialog.getSaveFileName(
            self, "Save to File",
            self.pathsconfig["dol"],
            "Game Executable (*.dol);;All files (*)")

        if filepath:
            with open("lib/minimap_locations.json", "r") as f:
                addresses_json = json.load(f)

            with open(filepath, "rb") as f:
                dol = DolFile(f)
                region = detect_dol_region(dol)

            addresses = addresses_json[region]

            item_list = ["None"]
            item_list.extend(addresses.keys())
            result, pos = FileSelect.open_file_list(self, item_list, "Select Track Slot")

            if result == "None" or result is None:
                return

            corner1x, corner1z, corner2x, corner2z, orientation = addresses[result]
            with open(filepath, "rb") as f:
                dol = DolFile(f)

            orientation_val = self.level_view.minimap.orientation
            if orientation_val not in (0, 1, 2, 3):
                raise RuntimeError(
                    "Invalid Orientation value: Must be in the range 0-3 but is {0}".format(orientation_val))

            dol.seek(int(orientation, 16))
            orientation_val = read_load_immediate_r0(dol)
            if orientation_val not in (0, 1, 2, 3):
                raise RuntimeError(
                    "Wrong Address, orientation value in DOL isn't in 0-3 range: {0}. Maybe you are using"
                    " a dol from a different game version?".format(orientation_val))

            dol.seek(int(orientation, 16))
            write_load_immediate_r0(dol, self.level_view.minimap.orientation)
            dol.seek(int(corner1x, 16))
            write_float(dol, self.level_view.minimap.corner1.x)
            dol.seek(int(corner1z, 16))
            write_float(dol, self.level_view.minimap.corner1.z)
            dol.seek(int(corner2x, 16))
            write_float(dol, self.level_view.minimap.corner2.x)
            dol.seek(int(corner2z, 16))
            write_float(dol, self.level_view.minimap.corner2.z)
            self.level_view.do_redraw()

            with open(filepath, "wb") as f:
                dol.save(f)

            self.pathsconfig["dol"] = filepath
            save_cfg(self.configuration)

    @catch_exception_with_dialog
    def action_load_coordinates_json(self):
        filepath, choosentype = QtWidgets.QFileDialog.getOpenFileName(
            self, "Open File",
            self.pathsconfig["minimap_json"],
            "Json File (*.json);;All files (*)")

        if filepath:
            with open(filepath, "r") as f:
                data = json.load(f)
                self.level_view.minimap.corner1.x = data["Top Left Corner X"]
                self.level_view.minimap.corner1.z = data["Top Left Corner Z"]
                self.level_view.minimap.corner2.x = data["Bottom Right Corner X"]
                self.level_view.minimap.corner2.z = data["Bottom Right Corner Z"]
                self.level_view.minimap.orientation = data["Orientation"]

            self.pathsconfig["minimap_json"] = filepath
            save_cfg(self.configuration)

    @catch_exception_with_dialog
    def action_save_coordinates_json(self):
        filepath, choosentype = QtWidgets.QFileDialog.getSaveFileName(
            self, "Save File",
            self.pathsconfig["minimap_json"],
            "Json File (*.json);;All files (*)")

        if filepath:
            data = {"Top Left Corner X": self.level_view.minimap.corner1.x,
                    "Top Left Corner Z": self.level_view.minimap.corner1.z,
                    "Bottom Right Corner X": self.level_view.minimap.corner2.x,
                    "Bottom Right Corner Z": self.level_view.minimap.corner2.z,
                    "Orientation": self.level_view.minimap.orientation}

            with open(filepath, "w") as f:
                json.dump(data, f, indent=4)

            self.pathsconfig["minimap_json"] = filepath
            save_cfg(self.configuration)

    @catch_exception_with_dialog
    def minimap_generator_action(self):
        if self.bco_coll is None:
            open_info_dialog('No BCO file has been loaded yet.', self)
            return

        with self.undo_history_disabled():
            show_minimap_generator(self)

    def action_choose_bco_area(self):
        if not isinstance(self.level_view.alternative_mesh, CollisionModel):
            QtWidgets.QMessageBox.information(self, "Collision Areas (BCO)",
                                              "No collision file is loaded.")
            return

        if self.collision_area_dialog is not None:
            self.collision_area_dialog.close()
            self.collision_area_dialog = None

        collision_model = self.level_view.alternative_mesh
        colltypes = tuple(sorted(collision_model.meshes))

        colltypegroups = {}
        for colltype in colltypes:
            colltypegroup = colltype & 0xFF00
            if colltypegroup not in colltypegroups:
                colltypegroups[colltypegroup] = []
            colltypegroups[colltypegroup].append(colltype)

        class DeselectableTableWidget(QtWidgets.QTreeWidget):
            def mousePressEvent(self, event):
                super().mousePressEvent(event)

                modelIndex = self.indexAt(event.pos())
                if not modelIndex.isValid():
                    self.clearSelection()

        tree_widget = DeselectableTableWidget()
        tree_widget.setColumnCount(2)
        tree_widget.setHeaderLabels(("Type", "Description"))

        def get_collision_type_desc(label):
            # http://wiki.tockdom.com/wiki/BCO_(File_Format)
            # https://mkdd.miraheze.org/wiki/BCO_(File_Format)#Collision_Flags

            group_descs = {
                "0x00__": "Medium Off-road",
                "0x01__": "Road",
                "0x02__": "Wall",
                "0x03__": "Medium Off-road",
                "0x04__": "Slippery Ice",
                "0x05__": "Dead zone",
                "0x06__": "Grassy Wall",
                "0x07__": "Boost",
                "0x08__": "Boost",
                "0x09__": "Cannon Boost",
                "0x0A__": "Dead zone",
                "0x0C__": "Weak Off-road",
                "0x0D__": "Teleport",
                "0x0E__": "Sand Dead zone",
                "0x0F__": "Wavy Dead zone",
                "0x10__": "Quicksand Dead zone",
                "0x11__": "Dead zone",
                "0x12__": "Kart-Only Wall",
                "0x13__": "Heavy Off-road",
                "0x37__": "Boost",
                "0x47__": "Boost",
            }

            return group_descs.get(label[:-2] + "__", "")

        for colltypegroup in sorted(colltypegroups):
            colltypes = colltypegroups[colltypegroup]

            if len(colltypes) == 1 and colltypegroup not in collision_model.hidden_collision_type_groups:
                colltype = colltypes[0]
                label = "0x{0:0{1}X}".format(colltype, 4)
                tree_widget_item = QtWidgets.QTreeWidgetItem(None, (label, ))
                tree_widget_item.setData(0, QtCore.Qt.UserRole + 1, colltype)
                tree_widget_item.setData(1, QtCore.Qt.DisplayRole, get_collision_type_desc(label))
                tree_widget_item.setCheckState(
                    0, QtCore.Qt.Checked
                    if colltype not in collision_model.hidden_collision_types
                    else QtCore.Qt.Unchecked)
                tree_widget.addTopLevelItem(tree_widget_item)
                continue

            label = "0x{0:0{1}X}".format(colltypegroup, 4)[:-2] + "__"
            tree_widget_item = QtWidgets.QTreeWidgetItem(None, (label, ))
            tree_widget_item.setData(0, QtCore.Qt.UserRole + 1, colltypegroup)
            tree_widget_item.setData(1, QtCore.Qt.DisplayRole, get_collision_type_desc(label))
            tree_widget_item.setCheckState(
                0, QtCore.Qt.Checked
                if colltypegroup not in collision_model.hidden_collision_type_groups
                else QtCore.Qt.Unchecked)
            tree_widget.addTopLevelItem(tree_widget_item)
            for colltype in colltypes:
                label = "0x{0:0{1}X}".format(colltype, 4)
                child_tree_widget_item = QtWidgets.QTreeWidgetItem(tree_widget_item, (label, ))
                child_tree_widget_item.setData(0, QtCore.Qt.UserRole + 1, colltype)
                child_tree_widget_item.setCheckState(
                    0, QtCore.Qt.Checked
                    if colltype not in collision_model.hidden_collision_types
                    else QtCore.Qt.Unchecked)

        def on_tree_widget_itemSelectionChanged(tree_widget=tree_widget):
            self.level_view.highlight_colltype = None

            for item in tree_widget.selectedItems():
                if item.childCount():
                    continue
                self.level_view.highlight_colltype = item.data(0, QtCore.Qt.UserRole + 1)
                break

            self.update_3d()

        all_items = tree_widget.findItems(
            "*",
            QtCore.Qt.MatchWrap | QtCore.Qt.MatchWildcard
            | QtCore.Qt.MatchRecursive)

        show_all_button = QtWidgets.QPushButton('Show All')
        hide_all_button = QtWidgets.QPushButton('Hide All')

        def update_both_all_buttons():
            checked_count = 0
            for item in all_items:
                checked = item.checkState(0) == QtCore.Qt.Checked
                if checked:
                    checked_count += 1

            show_all_button.setEnabled(checked_count < len(all_items))
            hide_all_button.setEnabled(checked_count)

        def on_tree_widget_itemChanged(item, column, tree_widget=tree_widget):
            for item in all_items:
                checked = item.checkState(0) == QtCore.Qt.Checked
                if item.childCount():
                    target_set = collision_model.hidden_collision_type_groups
                else:
                    target_set = collision_model.hidden_collision_types
                colltype = item.data(0, QtCore.Qt.UserRole + 1)
                if checked:
                    target_set.discard(colltype)
                else:
                    target_set.add(colltype)

            update_both_all_buttons()

            self.configuration["editor"]["hidden_collision_types"] = \
                ",".join(str(t) for t in collision_model.hidden_collision_types)
            self.configuration["editor"]["hidden_collision_type_groups"] = \
                ",".join(str(t) for t in collision_model.hidden_collision_type_groups)

            save_cfg(self.configuration)
            self.update_3d()

        tree_widget.itemSelectionChanged.connect(on_tree_widget_itemSelectionChanged)
        tree_widget.itemChanged.connect(on_tree_widget_itemChanged)

        tree_widget.expandAll()
        tree_widget.resizeColumnToContents(0)

        buttons_layout = QtWidgets.QHBoxLayout()
        buttons_layout.setContentsMargins(5, 5, 5, 5)
        buttons_layout.setSpacing(5)
        def on_show_all_button_clicked(checked):
            for item in all_items:
                item.setCheckState(0, QtCore.Qt.Checked)
        show_all_button.clicked.connect(on_show_all_button_clicked)
        def on_hide_all_button_clicked(checked):
            for item in all_items:
                item.setCheckState(0, QtCore.Qt.Unchecked)
        hide_all_button.clicked.connect(on_hide_all_button_clicked)
        buttons_layout.addWidget(show_all_button)
        buttons_layout.addWidget(hide_all_button)
        update_both_all_buttons()

        self.collision_area_dialog = QtWidgets.QDialog(self)
        self.collision_area_dialog.setWindowTitle("Collision Areas (BCO)")
        self.collision_area_dialog.setContentsMargins(0, 0, 0, 0)
        layout = QtWidgets.QVBoxLayout(self.collision_area_dialog)
        layout.setContentsMargins(0, 0, 0, 0)
        layout.setSpacing(0)
        layout.addWidget(tree_widget)
        layout.addLayout(buttons_layout)

        if "geometry" in self.configuration:
            geo_config = self.configuration["geometry"]

            def to_byte_array(byte_array: str) -> QtCore.QByteArray:
                return QtCore.QByteArray.fromBase64(byte_array.encode(encoding='ascii'))

            if "collision_window_geometry" in geo_config:
                self.collision_area_dialog.restoreGeometry(
                    to_byte_array(geo_config["collision_window_geometry"]))

        self.collision_area_dialog.show()

        def on_dialog_finished(result):
            _ = result
            if self.isVisible():
                self.save_geometry()

        self.collision_area_dialog.finished.connect(on_dialog_finished)

    def analyze_for_mistakes(self):
        analyzer_window = ErrorAnalyzer(self.level_file, parent=self)
        analyzer_window.exec()
        analyzer_window.deleteLater()

    def on_file_menu_aboutToShow(self):
        recent_files = self.get_recent_files_list()

        self.file_load_recent_menu.setEnabled(bool(recent_files))
        self.file_load_recent_menu.clear()

        for filepath in recent_files:
            recent_file_action = self.file_load_recent_menu.addAction(filepath)
            recent_file_action.triggered[bool].connect(
                lambda _checked, filepath=filepath: self.button_load_level(filepath))

    def on_filter_update(self):
        filters = []
        for object_toggle in self.visibility_menu.get_entries():
            if not object_toggle.action_view_toggle.isChecked():
                filters.append(object_toggle.action_view_toggle.text())
            if not object_toggle.action_select_toggle.isChecked():
                filters.append(object_toggle.action_select_toggle.text())

        self.editorconfig["filter_view"] = ','.join(filters)
        save_cfg(self.configuration)

        self.level_view.do_redraw()

    def on_cull_faces_triggered(self, checked):
        self.editorconfig["cull_faces"] = "True" if checked else "False"
        save_cfg(self.configuration)

        self.level_view.cull_faces = bool(checked)
        self.level_view.do_redraw()

    def on_default_geometry_changed(self, default_filetype):
        self.editorconfig["addi_file_on_load"] = default_filetype
        save_cfg(self.configuration)

        collision_actions = [self.auto_load_bco, self.auto_load_bmd, self.auto_load_none, self.auto_load_choose]
        collision_options = ("BCO", "BMD", "None", "Choose")

        for i, option in enumerate(collision_options):
            collision_actions[i].setChecked(option == default_filetype)

    def change_to_topdownview(self, checked):
        if checked:
            self.level_view.change_from_3d_to_topdown()

    def change_to_3dview(self, checked):
        if checked:
            self.level_view.change_from_topdown_to_3d()
            self.statusbar.clearMessage()

            # After switching to the 3D view for the first time, the view will be framed to help
            # users find the objects in the world.
            if self.first_time_3dview:
                self.first_time_3dview = False
                self.frame_selection(adjust_zoom=True)

    def setup_ui_toolbar(self):
        # self.toolbar = QtWidgets.QToolBar("Test", self)
        # self.toolbar.addAction(QtGui.QAction("TestToolbar", self))
        # self.toolbar.addAction(QtGui.QAction("TestToolbar2", self))
        # self.toolbar.addAction(QtGui.QAction("TestToolbar3", self))

        # self.toolbar2 = QtWidgets.QToolBar("Second Toolbar", self)
        # self.toolbar2.addAction(QtGui.QAction("I like cake", self))

        # self.addToolBar(self.toolbar)
        # self.addToolBarBreak()
        # self.addToolBar(self.toolbar2)
        pass

    def connect_actions(self):
        self.level_view.select_update.connect(self.action_update_info)
        self.level_view.select_update.connect(self.select_from_3d_to_treeview)
        #self.pik_control.lineedit_coordinatex.textChanged.connect(self.create_field_edit_action("coordinatex"))
        #self.pik_control.lineedit_coordinatey.textChanged.connect(self.create_field_edit_action("coordinatey"))
        #self.pik_control.lineedit_coordinatez.textChanged.connect(self.create_field_edit_action("coordinatez"))

        #self.pik_control.lineedit_rotationx.textChanged.connect(self.create_field_edit_action("rotationx"))
        #self.pik_control.lineedit_rotationy.textChanged.connect(self.create_field_edit_action("rotationy"))
        #self.pik_control.lineedit_rotationz.textChanged.connect(self.create_field_edit_action("rotationz"))

        self.level_view.position_update.connect(self.action_update_position)

        self.level_view.customContextMenuRequested.connect(self.mapview_showcontextmenu)

        self.pik_control.button_add_object.clicked.connect(
            lambda _checked: self.button_open_add_item_window())
        #self.pik_control.button_move_object.pressed.connect(self.button_move_objects)
        self.level_view.move_points.connect(self.action_move_objects)
        self.level_view.height_update.connect(self.action_change_object_heights)
        self.level_view.create_waypoint.connect(self.action_add_object)
        self.level_view.create_waypoint_3d.connect(self.action_add_object_3d)
        self.pik_control.button_ground_object.clicked.connect(
            lambda _checked: self.action_ground_objects())
        self.pik_control.button_remove_object.clicked.connect(
            lambda _checked: self.action_delete_objects())

        delete_shortcut = QtGui.QShortcut(QtGui.QKeySequence(QtCore.Qt.Key_Delete), self)
        delete_shortcut.activated.connect(self.action_delete_objects)

        self.level_view.rotate_current.connect(self.action_rotate_object)
        self.leveldatatreeview.select_all.connect(self.select_all_of_group)
        self.leveldatatreeview.reverse.connect(self.reverse_all_of_group)
        self.leveldatatreeview.duplicate.connect(self.duplicate_group)
        self.leveldatatreeview.split.connect(self.split_group)
        self.leveldatatreeview.split_checkpoint.connect(self.split_group_checkpoint)

    def split_group_checkpoint(self, group_item, item):
        group = group_item.bound_to
        point = item.bound_to

        if point == group.points[-1]:
            return

        """# Get an unused link to connect the groups with
        new_link = self.level_file.enemypointgroups.new_link_id()
        if new_link >= 2**14:
            raise RuntimeError("Too many links, cannot create more")
        """

        # Get new hopefully unused group id
        new_id = self.level_file.checkpoints.new_group_id()
        new_group = group.copy_group_after(new_id, point)
        self.level_file.checkpoints.groups.append(new_group)
        group.remove_after(point)
        new_group.prevlinks = [group.grouplink, -1, -1, -1]
        new_group.nextlinks = deepcopy(group.nextgroup)
        group.nextgroup = [new_group.grouplink, -1, -1, -1]

        self.leveldatatreeview.set_objects(self.level_file)
        self.update_3d()
        self.set_has_unsaved_changes(True)

    def split_group(self, group_item, item):
        group = group_item.bound_to
        point = item.bound_to

        if point == group.points[-1]:
            return

        # Get an unused link to connect the groups with
        new_link = self.level_file.enemypointgroups.new_link_id()
        if new_link >= 2**14:
            raise RuntimeError("Too many links, cannot create more")

        # Get new hopefully unused group id
        new_id = self.level_file.enemypointgroups.new_group_id()
        new_group = group.copy_group_after(new_id, point)
        self.level_file.enemypointgroups.groups.append(new_group)
        group.remove_after(point)

        group.points[-1].link = new_group.points[0].link = new_link

        self.leveldatatreeview.set_objects(self.level_file)
        self.update_3d()
        self.set_has_unsaved_changes(True)

    def duplicate_group(self, item):
        group = item.bound_to
        if isinstance(group, libbol.EnemyPointGroup):
            new_id = len(self.level_file.enemypointgroups.groups)
            new_group = group.copy_group(new_id)
            self.level_file.enemypointgroups.groups.append(new_group)

            self.leveldatatreeview.set_objects(self.level_file)
            self.update_3d()
            self.set_has_unsaved_changes(True)

    def reverse_all_of_group(self, item):
        group = item.bound_to
        if isinstance(group, libbol.CheckpointGroup):
            group.points.reverse()
            for point in group.points:
                start = point.start
                point.start = point.end
                point.end = start
        elif isinstance(group, libbol.EnemyPointGroup):
            group.points.reverse()
        elif isinstance(group, libbol.Route):
            group.points.reverse()

        self.leveldatatreeview.set_objects(self.level_file)
        self.update_3d()

    def select_all_of_group(self, item):
        group = item.bound_to
        self.level_view.selected = []
        self.level_view.selected_positions = []
        self.level_view.selected_rotations = []
        for point in group.points:
            self.level_view.selected.append(point)

            if isinstance(group, libbol.CheckpointGroup):
                self.level_view.selected_positions.append(point.start)
                self.level_view.selected_positions.append(point.end)
            else:
                self.level_view.selected_positions.append(point.position)
        self.update_3d()

    def action_open_rotationedit_window(self):
        if self.edit_spawn_window is None:
            self.edit_spawn_window = mkdd_widgets.SpawnpointEditor()
            self.edit_spawn_window.position.setText("{0}, {1}, {2}".format(
                self.pikmin_gen_file.startpos_x, self.pikmin_gen_file.startpos_y, self.pikmin_gen_file.startpos_z
            ))
            self.edit_spawn_window.rotation.setText(str(self.pikmin_gen_file.startdir))
            self.edit_spawn_window.closing.connect(self.action_close_edit_startpos_window)
            self.edit_spawn_window.button_savetext.clicked.connect(
                lambda _checked: self.action_save_startpos())
            self.edit_spawn_window.show()

    def update_recent_files_list(self, filepath):
        filepath = os.path.abspath(os.path.normpath(filepath))

        recent_files = self.get_recent_files_list()
        if filepath in recent_files:
            recent_files.remove(filepath)

        recent_files.insert(0, filepath)
        recent_files = recent_files[:10]

        self.configuration["recent files"] = {}
        recent_files_config = self.configuration["recent files"]

        for i, filepath in enumerate(recent_files):
            config_entry = f"file{i}"
            recent_files_config[config_entry] = filepath

    def get_recent_files_list(self):
        if "recent files" not in self.configuration:
            self.configuration["recent files"] = {}
        recent_files_config = self.configuration["recent files"]

        recent_files = []
        for i in range(10):
            config_entry = f"file{i}"
            if config_entry in recent_files_config:
                recent_files.append(recent_files_config[config_entry])

        return recent_files

    #@catch_exception
    def button_load_level(self, filepath=None, update_config=True):
        if filepath is None:
            filepath, chosentype = QtWidgets.QFileDialog.getOpenFileName(
                self, "Open File",
                self.pathsconfig["bol"],
                "BOL files (*.bol);;Archived files (*.arc);;All files (*)",
                self.last_chosen_type)
        else:
            chosentype = None

        if filepath:
            if chosentype is not None:
                self.last_chosen_type = chosentype
            print("Resetting editor")
            self.reset()
            print("Reset done")
            print("Chosen file type:", chosentype)
            if chosentype == "Archived files (*.arc)" or filepath.endswith(".arc"):
                with open(filepath, "rb") as f:
                    try:
                        self.loaded_archive = Archive.from_file(f)
                        root_name = self.loaded_archive.root.name
                        coursename = find_file(self.loaded_archive.root, "_course.bol")
                        bol_file = self.loaded_archive[root_name + "/" + coursename]
                        bol_data = BOL.from_file(bol_file)
                        self.setup_bol_file(bol_data, filepath, update_config)
                        self.leveldatatreeview.set_objects(bol_data)
                        self.current_gen_path = filepath
                        self.loaded_archive_file = coursename
                    except Exception as error:
                        print("Error appeared while loading:", error)
                        traceback.print_exc()
                        open_error_dialog(str(error), self)
                        self.loaded_archive = None
                        self.loaded_archive_file = None
                        return

                bmdfile = get_file_safe(self.loaded_archive.root, "_course.bmd")
                collisionfile = get_file_safe(self.loaded_archive.root, "_course.bco")

                if self.editorconfig["addi_file_on_load"] == "Choose":
                    try:
                        additional_files = []

                        if bmdfile is not None:
                            additional_files.append(os.path.basename(bmdfile.name) + " (3D Model)")
                        if collisionfile is not None:
                            additional_files.append(os.path.basename(collisionfile.name) + " (3D Collision)")

                        if len(additional_files) > 0:
                            additional_files.append("None")
                            self.load_optional_3d_file_arc(additional_files, bmdfile, collisionfile, filepath)
                        else:
                            self.clear_collision()
                    except Exception as error:
                        print("Error appeared while loading:", error)
                        traceback.print_exc()
                        open_error_dialog(str(error), self)
                elif bmdfile is not None and self.editorconfig["addi_file_on_load"] == "BMD":
                    self.load_bmd_from_arc(bmdfile, filepath)
                elif collisionfile is not None and self.editorconfig["addi_file_on_load"] == "BCO":
                    self.load_bco_from_arc(collisionfile, filepath)
                elif self.editorconfig["addi_file_on_load"] == "None":
                    self.clear_collision()

            else:
                with open(filepath, "rb") as f:
                    try:
                        bol_file = BOL.from_file(f)
                        self.setup_bol_file(bol_file, filepath, update_config)
                        self.leveldatatreeview.set_objects(bol_file)
                        self.current_gen_path = filepath
                    except Exception as error:
                        print("Error appeared while loading:", error)
                        traceback.print_exc()
                        open_error_dialog(str(error), self)

                    if filepath.endswith("_course.bol"):
                        filepath_base = filepath[:-11]
                        bmdfile = filepath_base+"_course.bmd"
                        collisionfile = filepath_base+"_course.bco"

                        if self.editorconfig["addi_file_on_load"] == "Choose":

                            additional_files = []

                            if os.path.exists(bmdfile):
                                additional_files.append(os.path.basename(bmdfile) + " (3D Model)")
                            if os.path.exists(collisionfile):
                                additional_files.append(os.path.basename(collisionfile) + " (3D Collision)")

                            if len(additional_files) > 0:
                                additional_files.append("None")
                                self.load_optional_3d_file(additional_files, bmdfile, collisionfile)
                            else:
                                self.clear_collision()
                        elif bmdfile is not None and self.editorconfig["addi_file_on_load"] == "BMD":
                            if os.path.isfile(bmdfile):
                                self.load_optional_bmd(bmdfile)
                        elif collisionfile is not None and self.editorconfig["addi_file_on_load"] == "BCO":
                            if os.path.isfile(collisionfile):
                                self.load_optional_bco(collisionfile)
                        elif self.editorconfig["addi_file_on_load"] == "None":
                            self.clear_collision()

            self.update_3d()

    def load_optional_3d_file(self, additional_files, bmdfile, collisionfile):
        choice, pos = FileSelect.open_file_list(self, additional_files,
                                                "Select additional file to load", startat=0)

        self.clear_collision()

        if not choice:
            return

        if choice.endswith("(3D Model)"):
            self.load_optional_bmd(bmdfile)

        elif choice.endswith("(3D Collision)"):
            self.load_optional_bco(collisionfile)

    def load_optional_bmd(self, bmdfile):
        alternative_mesh = load_textured_bmd(bmdfile)
        with open("lib/temp/temp.obj", "r") as f:
            verts, faces, normals = py_obj.read_obj(f)

        self.setup_collision(verts, faces, bmdfile, alternative_mesh)

    def load_optional_bco(self, collisionfile):
        bco_coll = RacetrackCollision()
        verts = []
        faces = []

        with open(collisionfile, "rb") as f:
            bco_coll.load_file(f)
        self.bco_coll = bco_coll

        for vert in bco_coll.vertices:
            verts.append(vert)

        for v1, v2, v3, collision_type, rest in bco_coll.triangles:
            faces.append(((v1 + 1, None), (v2 + 1, None), (v3 + 1, None)))
        model = CollisionModel(bco_coll)
        self.setup_collision(verts, faces, collisionfile, alternative_mesh=model)

    def load_optional_3d_file_arc(self, additional_files, bmdfile, collisionfile, arcfilepath):
        choice, pos = FileSelect.open_file_list(self, additional_files,
                                                "Select additional file to load", startat=0)

        self.clear_collision()

        if not choice:
            return

        if choice.endswith("(3D Model)"):
            self.load_bmd_from_arc(bmdfile, arcfilepath)

        elif choice.endswith("(3D Collision)"):
            self.load_bco_from_arc(collisionfile, arcfilepath)

    def load_bmd_from_arc(self, bmdfile, arcfilepath):
        with open("lib/temp/temp.bmd", "wb") as f:
            f.write(bmdfile.getvalue())

        bmdpath = "lib/temp/temp.bmd"
        alternative_mesh = load_textured_bmd(bmdpath)
        with open("lib/temp/temp.obj", "r") as f:
            verts, faces, normals = py_obj.read_obj(f)

        self.setup_collision(verts, faces, arcfilepath, alternative_mesh)

    def load_bco_from_arc(self, collisionfile, arcfilepath):
        bco_coll = RacetrackCollision()
        verts = []
        faces = []

        bco_coll.load_file(collisionfile)
        self.bco_coll = bco_coll

        for vert in bco_coll.vertices:
            verts.append(vert)

        for v1, v2, v3, collision_type, rest in bco_coll.triangles:
            faces.append(((v1 + 1, None), (v2 + 1, None), (v3 + 1, None)))
        model = CollisionModel(bco_coll)
        self.setup_collision(verts, faces, arcfilepath, alternative_mesh=model)

    def load_file(self, filepath, additional=None):
        if filepath.endswith('.bol'):
            return self.load_bol_file(filepath, additional=additional)

        if filepath.endswith('.arc'):
            return self.load_arc_file(filepath, additional=additional)

    def load_bol_file(self, filepath, additional=None):
        with open(filepath, "rb") as f:
            bol_file = BOL.from_file(f)
            self.setup_bol_file(bol_file, filepath)
            self.leveldatatreeview.set_objects(bol_file)
            self.current_gen_path = filepath

        if not filepath.endswith('_course.bol'):
            return

        self.clear_collision()

        if additional == 'model':
            bmdfile = filepath[:-len('.bol')] + ".bmd"
            if not os.path.isfile(bmdfile):
                return

            alternative_mesh = load_textured_bmd(bmdfile)
            with open("lib/temp/temp.obj", "r") as f:
                verts, faces, normals = py_obj.read_obj(f)

            self.setup_collision(verts, faces, bmdfile, alternative_mesh)

        elif additional == 'collision':
            collisionfile = filepath[:-len('.bol')] + ".bco"
            if not os.path.isfile(collisionfile):
                return

            bco_coll = RacetrackCollision()
            with open(collisionfile, "rb") as f:
                bco_coll.load_file(f)
            self.bco_coll = bco_coll

            verts = []
            for vert in bco_coll.vertices:
                verts.append(vert)

            faces = []
            for v1, v2, v3, collision_type, rest in bco_coll.triangles:
                faces.append(((v1 + 1, None), (v2 + 1, None), (v3 + 1, None)))

            model = CollisionModel(bco_coll)
            self.setup_collision(verts, faces, collisionfile, alternative_mesh=model)

        QtCore.QTimer.singleShot(0, self.update_3d)

    def load_arc_file(self, filepath, additional=None):
        with open(filepath, "rb") as f:
            try:
                self.loaded_archive = Archive.from_file(f)
                root_name = self.loaded_archive.root.name
                coursename = find_file(self.loaded_archive.root, "_course.bol")
                bol_file = self.loaded_archive[root_name + "/" + coursename]
                bol_data = BOL.from_file(bol_file)
                self.setup_bol_file(bol_data, filepath)
                self.leveldatatreeview.set_objects(bol_data)
                self.current_gen_path = filepath
                self.loaded_archive_file = coursename
            except:
                self.loaded_archive = None
                self.loaded_archive_file = None
                raise

        self.clear_collision()

        if additional == 'model':
            bmdfile = get_file_safe(self.loaded_archive.root, "_course.bmd")
            if bmdfile is None:
                return

            bmdpath = "lib/temp/temp.bmd"
            with open(bmdpath, "wb") as f:
                f.write(bmdfile.getvalue())

            alternative_mesh = load_textured_bmd(bmdpath)
            with open("lib/temp/temp.obj", "r") as f:
                verts, faces, normals = py_obj.read_obj(f)

            self.setup_collision(verts, faces, filepath, alternative_mesh)

        elif additional == 'collision':
            collisionfile = get_file_safe(self.loaded_archive.root, "_course.bco")
            if collisionfile is None:
                return

            bco_coll = RacetrackCollision()
            bco_coll.load_file(collisionfile)
            self.bco_coll = bco_coll

            verts = []
            for vert in bco_coll.vertices:
                verts.append(vert)

            faces = []
            for v1, v2, v3, collision_type, rest in bco_coll.triangles:
                faces.append(((v1 + 1, None), (v2 + 1, None), (v3 + 1, None)))

            model = CollisionModel(bco_coll)
            self.setup_collision(verts, faces, filepath, alternative_mesh=model)

        QtCore.QTimer.singleShot(0, self.update_3d)

    def setup_bol_file(self, bol_file, filepath, update_config=True):
        self.level_file = bol_file
        self.level_view.level_file = self.level_file
        # self.pikmin_gen_view.update()
        self.level_view.do_redraw()

        self.on_document_potentially_changed(update_unsaved_changes=False)

        print("File loaded")
        # self.bw_map_screen.update()
        # path_parts = path.split(filepath)
        self.set_base_window_title(filepath)
        if update_config:
            self.pathsconfig["bol"] = filepath
            self.update_recent_files_list(filepath)
            save_cfg(self.configuration)
        self.current_gen_path = filepath

    @catch_exception_with_dialog
    def button_save_level(self, *args, **kwargs):
        if self.current_gen_path is not None:
            if self.loaded_archive is not None:
                assert self.loaded_archive_file is not None
                root_name = self.loaded_archive.root.name
                file = self.loaded_archive[root_name + "/" + self.loaded_archive_file]
                file.seek(0)

                self.level_file.write(file)

                with open(self.current_gen_path, "wb") as f:
                    self.loaded_archive.write_arc(f)

                self.set_has_unsaved_changes(False)
                self.statusbar.showMessage("Saved to {0}".format(self.current_gen_path))

            else:
                with open(self.current_gen_path, "wb") as f:
                    self.level_file.write(f)
                    self.set_has_unsaved_changes(False)

                    self.statusbar.showMessage("Saved to {0}".format(self.current_gen_path))
        else:
            self.button_save_level_as()

    def button_save_level_as(self, *args, **kwargs):
        self._button_save_level_as(True, *args, **kwargs)

    def button_save_level_copy_as(self, *args, **kwargs):
        self._button_save_level_as(False, *args, **kwargs)

    @catch_exception_with_dialog
    def _button_save_level_as(self, modify_current_path, *args, **kwargs):
        filepath, choosentype = QtWidgets.QFileDialog.getSaveFileName(
            self, "Save File",
            self.pathsconfig["bol"],
            "MKDD Track Data (*.bol);;Archived files (*.arc);;All files (*)",
            self.last_chosen_type)

        if filepath:
            if choosentype == "Archived files (*.arc)" or filepath.endswith(".arc"):
                if self.loaded_archive is None or self.loaded_archive_file is None:
                    with open(filepath, "rb") as f:
                        self.loaded_archive = Archive.from_file(f)

                self.loaded_archive_file = find_file(self.loaded_archive.root, "_course.bol")
                root_name = self.loaded_archive.root.name
                file = self.loaded_archive[root_name + "/" + self.loaded_archive_file]
                file.seek(0)

                self.level_file.write(file)

                with open(filepath, "wb") as f:
                    self.loaded_archive.write_arc(f)

                self.set_has_unsaved_changes(False)
                self.statusbar.showMessage("Saved to {0}".format(filepath))
            else:
                with open(filepath, "wb") as f:
                    self.level_file.write(f)

                    self.set_has_unsaved_changes(False)

            self.pathsconfig["bol"] = filepath
            save_cfg(self.configuration)

            if modify_current_path:
                self.current_gen_path = filepath
                self.set_base_window_title(filepath)

            self.statusbar.showMessage("Saved to {0}".format(filepath))




    def button_load_collision(self):
        try:
            filepath, choosentype = QtWidgets.QFileDialog.getOpenFileName(
                self, "Open File",
                self.pathsconfig["collision"],
                "Collision (*.obj);;All files (*)")

            if not filepath:
                return

            with open(filepath, "r") as f:
                verts, faces, normals = py_obj.read_obj(f)
            alternative_mesh = TexturedModel.from_obj_path(filepath, rotate=True)

            self.setup_collision(verts, faces, filepath, alternative_mesh)

        except Exception as e:
            traceback.print_exc()
            open_error_dialog(str(e), self)

        finally:
            self.update_3d()

    def button_load_collision_bmd(self):
        try:
            filepath, choosentype = QtWidgets.QFileDialog.getOpenFileName(
                self, "Open File",
                self.pathsconfig["collision"],
                "Course Model (*.bmd);;Archived files (*.arc);;All files (*)")

            if not filepath:
                return
            bmdpath = filepath
            clear_temp_folder()
            if choosentype == "Archived files (*.arc)" or filepath.endswith(".arc"):
                with open(filepath, "rb") as f:
                    rarc = Archive.from_file(f)

                root_name = rarc.root.name
                bmd_filename = find_file(rarc.root, "_course.bmd")
                bmd = rarc[root_name][bmd_filename]
                with open("lib/temp/temp.bmd", "wb") as f:
                    f.write(bmd.getvalue())

                bmdpath = "lib/temp/temp.bmd"

            self.clear_collision()

            alternative_mesh = load_textured_bmd(bmdpath)
            with open("lib/temp/temp.obj", "r") as f:
                verts, faces, normals = py_obj.read_obj(f)

            self.setup_collision(verts, faces, filepath, alternative_mesh)

        except Exception as e:
            traceback.print_exc()
            open_error_dialog(str(e), self)

        finally:
            self.update_3d()

    def button_load_collision_bco(self):
        try:
            filepath, choosentype = QtWidgets.QFileDialog.getOpenFileName(
                self, "Open File",
                self.pathsconfig["collision"],
                "MKDD Collision (*.bco);;Archived files (*.arc);;All files (*)")
            if filepath:
                bco_coll = RacetrackCollision()
                verts = []
                faces = []

                if choosentype == "Archived files (*.arc)" or filepath.endswith(".arc"):
                    with open(filepath, "rb") as f:
                        rarc = Archive.from_file(f)


                    root_name = rarc.root.name
                    collision_file = find_file(rarc.root, "_course.bco")
                    bco = rarc[root_name][collision_file]
                    bco_coll.load_file(bco)
                    self.bco_coll = bco_coll
                else:
                    with open(filepath, "rb") as f:
                        bco_coll.load_file(f)
                    self.bco_coll = bco_coll

                for vert in bco_coll.vertices:
                    verts.append(vert)

                for v1, v2, v3, collision_type, rest in bco_coll.triangles:
                    faces.append(((v1+1, None), (v2+1, None), (v3+1, None)))
                model = CollisionModel(bco_coll)
                self.setup_collision(verts, faces, filepath, alternative_mesh=model)

        except Exception as e:
            traceback.print_exc()
            open_error_dialog(str(e), self)

        finally:
            self.update_3d()

    def clear_collision(self):
        self.bco_coll = None
        self.level_view.clear_collision()

        # Synchronously force a draw operation to provide immediate feedback.
        self.level_view.update()
        QtWidgets.QApplication.instance().processEvents()

    def setup_collision(self, verts, faces, filepath, alternative_mesh=None):
        self.level_view.set_collision(verts, faces, alternative_mesh)
        self.pathsconfig["collision"] = filepath
        editor_config = self.configuration["editor"]
        alternative_mesh.hidden_collision_types = \
            set(int(t) for t in editor_config.get("hidden_collision_types", "").split(",") if t)
        alternative_mesh.hidden_collision_type_groups = \
            set(int(t) for t in editor_config.get("hidden_collision_type_groups", "").split(",") if t)
        save_cfg(self.configuration)

    def action_close_edit_startpos_window(self):
        self.edit_spawn_window.destroy()
        self.edit_spawn_window = None

    @catch_exception_with_dialog
    def action_save_startpos(self):
        pos, direction = self.edit_spawn_window.get_pos_dir()
        self.pikmin_gen_file.startpos_x = pos[0]
        self.pikmin_gen_file.startpos_y = pos[1]
        self.pikmin_gen_file.startpos_z = pos[2]
        self.pikmin_gen_file.startdir = direction

        #self.pikmin_gen_view.update()
        self.pikmin_gen_view.do_redraw()
        self.set_has_unsaved_changes(True)

    def button_open_add_item_window(self):
        self.add_object_window.update_label()
        self.next_checkpoint_start_position = None

        accepted = self.add_object_window.exec()
        if accepted:
            self.add_item_window_save()
        else:
            self.level_view.set_mouse_mode(mkdd_widgets.MOUSE_MODE_NONE)
            self.pik_control.button_add_object.setChecked(False)

        self.update_3d()

    def shortcut_open_add_item_window(self):
        self.button_open_add_item_window()

    def select_tree_item_bound_to(self, obj):
        # Iteratively traverse all the tree widget items.
        pending_items = [self.leveldatatreeview.invisibleRootItem()]
        while pending_items:
            item = pending_items.pop(0)
            for child_index in range(item.childCount()):
                child_item = item.child(child_index)

                # Check whether the item contains any item that happens to be bound to the target
                # object.
                bound_item = get_treeitem(child_item, obj)
                if bound_item is not None:
                    # If found, deselect current selection, and select the new item.
                    for selected_item in self.leveldatatreeview.selectedItems():
                        selected_item.setSelected(False)
                    bound_item.setSelected(True)

                    # Ensure that the new item is visible.
                    parent_item = bound_item.parent()
                    while parent_item is not None:
                        parent_item.setExpanded(True)
                        parent_item = parent_item.parent()
                    self.leveldatatreeview.scrollToItem(bound_item)

                    return
                else:
                    pending_items.append(child_item)

    def add_item_window_save(self):
        self.object_to_be_added = self.add_object_window.get_content()
        if self.object_to_be_added is None:
            return

        obj = self.object_to_be_added[0]

        if isinstance(obj, (libbol.EnemyPointGroup, libbol.CheckpointGroup, libbol.Route,
                            libbol.LightParam, libbol.MGEntry)):
            obj = deepcopy(obj)

            if isinstance(obj, libbol.EnemyPointGroup):
                self.level_file.enemypointgroups.groups.append(obj)
            elif isinstance(obj, libbol.CheckpointGroup):
                self.level_file.checkpoints.groups.append(obj)
            elif isinstance(obj, libbol.Route):
                self.level_file.routes.append(obj)
            elif isinstance(obj, libbol.LightParam):
                self.level_file.lightparams.append(obj)
            elif isinstance(obj, libbol.MGEntry):
                self.level_file.mgentries.append(obj)

            self.object_to_be_added = None
            self.pik_control.button_add_object.setChecked(False)
            self.level_view.set_mouse_mode(mkdd_widgets.MOUSE_MODE_NONE)
            self.leveldatatreeview.set_objects(self.level_file)

            self.select_tree_item_bound_to(obj)

        elif self.object_to_be_added is not None:
            self.pik_control.button_add_object.setChecked(True)
            self.level_view.set_mouse_mode(mkdd_widgets.MOUSE_MODE_ADDWP)

    @catch_exception
    def action_add_object(self, x, z):
        y = 0
        object, group, position = self.object_to_be_added
        #if self.editorconfig.getboolean("GroundObjectsWhenAdding") is True:
        if isinstance(object, libbol.Checkpoint):
            y = object.start.y
        else:
            if self.level_view.collision is not None:
                y_collided = self.level_view.collision.collide_ray_downwards(x, z)
                if y_collided is not None:
                    y = y_collided

        self.action_add_object_3d(x, y, z)

    @catch_exception
    def action_add_object_3d(self, x, y, z):
        object, group, position = self.object_to_be_added
        if position is not None and position < 0:
            position = 99999999 # this forces insertion at the end of the list

        if isinstance(object, libbol.Checkpoint):
            if self.next_checkpoint_start_position is not None:
                placeobject = deepcopy(object)

                x1, y1, z1 = self.next_checkpoint_start_position
                self.next_checkpoint_start_position = None

                placeobject.start.x = x1
                placeobject.start.y = y1
                placeobject.start.z = z1

                placeobject.end.x = x
                placeobject.end.y = y
                placeobject.end.z = z

                # For convenience, create a group if none exists yet.
                if group == 0 and not self.level_file.checkpoints.groups:
                    self.level_file.checkpoints.groups.append(libbol.CheckpointGroup.new())
                insertion_index = position
                # If a selection exists, use it as reference for the insertion point.
                selected_items = self.leveldatatreeview.selectedItems()
                if selected_items:
                    selected_item = selected_items[-1]
                    if isinstance(selected_item.bound_to, libbol.Checkpoint):
                        group = selected_item.parent().get_index_in_parent()
                        insertion_index = selected_item.get_index_in_parent() + 1
                    elif isinstance(selected_item.bound_to, libbol.CheckpointGroup):
                        group = selected_item.get_index_in_parent()
                        insertion_index = 0

                self.level_file.checkpoints.groups[group].points.insert(
                    insertion_index, placeobject)
                self.level_view.do_redraw()
                self.set_has_unsaved_changes(True)
                self.leveldatatreeview.set_objects(self.level_file)

                self.select_tree_item_bound_to(placeobject)
            else:
                self.next_checkpoint_start_position = (x, y, z)

        else:
            placeobject = deepcopy(object)
            placeobject.position.x = x
            placeobject.position.y = y
            placeobject.position.z = z

            if isinstance(object, libbol.EnemyPoint):
                # For convenience, create a group if none exists yet.
                if group == 0 and not self.level_file.enemypointgroups.groups:
                    self.level_file.enemypointgroups.groups.append(libbol.EnemyPointGroup.new())
                placeobject.group = group
                insertion_index = position
                # If a selection exists, use it as reference for the insertion point.
                selected_items = self.leveldatatreeview.selectedItems()
                if selected_items:
                    selected_item = selected_items[-1]
                    if isinstance(selected_item.bound_to, libbol.EnemyPoint):
                        placeobject.group = selected_item.parent().get_index_in_parent()
                        insertion_index = selected_item.get_index_in_parent() + 1
                    elif isinstance(selected_item.bound_to, libbol.EnemyPointGroup):
                        placeobject.group = selected_item.get_index_in_parent()
                        insertion_index = 0
                self.level_file.enemypointgroups.groups[placeobject.group].points.insert(
                    insertion_index, placeobject)
            elif isinstance(object, libbol.RoutePoint):
                # For convenience, create a group if none exists yet.
                if group == 0 and not self.level_file.routes:
                    self.level_file.routes.append(libbol.Route.new())
                insertion_index = position
                # If a selection exists, use it as reference for the insertion point.
                selected_items = self.leveldatatreeview.selectedItems()
                if selected_items:
                    selected_item = selected_items[-1]
                    if isinstance(selected_item.bound_to, libbol.RoutePoint):
                        group = selected_item.parent().get_index_in_parent()
                        insertion_index = selected_item.get_index_in_parent() + 1
                    elif isinstance(selected_item.bound_to, libbol.Route):
                        group = selected_item.get_index_in_parent()
                        insertion_index = 0
                self.level_file.routes[group].points.insert(insertion_index, placeobject)
            elif isinstance(object, libbol.MapObject):
                self.level_file.objects.objects.append(placeobject)
            elif isinstance(object, libbol.KartStartPoint):
                self.level_file.kartpoints.positions.append(placeobject)
            elif isinstance(object, libbol.JugemPoint):
                if group == -1:
                    self.level_file.add_respawn(placeobject)
                else:
                    self.level_file.respawnpoints.append(placeobject)
            elif isinstance(object, libbol.Area):
                self.level_file.areas.areas.append(placeobject)
            elif isinstance(object, libbol.Camera):
                self.level_file.cameras.append(placeobject)
            else:
                raise RuntimeError("Unknown object type {0}".format(type(object)))

            self.level_view.do_redraw()
            self.leveldatatreeview.set_objects(self.level_file)
            self.set_has_unsaved_changes(True)

            self.select_tree_item_bound_to(placeobject)

    def button_side_button_action(self, option, obj=None):
        #stop adding new stuff
        self.pik_control.button_add_object.setChecked(False)
        self.level_view.set_mouse_mode(mkdd_widgets.MOUSE_MODE_NONE)
        self.object_to_be_added = None

        if option == "add_enemypath":
            self.level_file.enemypointgroups.add_group()
            self.level_view.selected = [self.level_file.enemypointgroups.groups[-1]]
            self.level_view.selected_positions = []
            self.level_view.selected_rotations = []
        elif option == "add_enemypoints":
            if isinstance(obj, libbol.EnemyPointGroup):
                group_id = obj.id
                pos = 0
            else:
                group_id = obj.group
                group: libbol.EnemyPointGroup = self.level_file.enemypointgroups.groups[obj.group]
                pos = group.get_index_of_point(obj)
            self.object_to_be_added = [libbol.EnemyPoint.new(), group_id, pos + 1]
            self.pik_control.button_add_object.setChecked(True)
            self.level_view.set_mouse_mode(mkdd_widgets.MOUSE_MODE_ADDWP)

        elif option == "add_checkpointgroup":
            self.level_file.checkpoints.add_group()
            self.level_view.selected = [self.level_file.checkpoints.groups[-1]]
            self.level_view.selected_positions = []
            self.level_view.selected_rotations = []
        elif option == "add_checkpoints":
            if isinstance(obj, libbol.CheckpointGroup):
                group_id = obj.grouplink
                pos = 0
            else:
                group_id, pos = self.level_file.checkpoints.find_group_of_point(obj)
            self.object_to_be_added = [libbol.Checkpoint.new(), group_id, pos + 1]
            self.pik_control.button_add_object.setChecked(True)
            self.level_view.set_mouse_mode(mkdd_widgets.MOUSE_MODE_ADDWP)
        elif option == "add_route":
            self.level_file.routes.append(libbol.Route.new())
        elif option == "add_routepoints":
            if isinstance(obj, libbol.Route):
                group_id = self.level_file.routes.index(obj)
                pos = 0
            else:
                group_id = -1
                for i, route in enumerate(self.level_file.routes):
                    if obj in route.points:
                        group_id = i
                        break
                pos = self.level_file.routes[group_id].get_index_of_point(obj)
            self.object_to_be_added = [libbol.RoutePoint.new(), group_id, pos + 1]
            self.pik_control.button_add_object.setChecked(True)
            self.level_view.set_mouse_mode(mkdd_widgets.MOUSE_MODE_ADDWP)
        elif option == "add_startpoint":
            self.object_to_be_added = [libbol.KartStartPoint.new(), -1, -1]
            self.pik_control.button_add_object.setChecked(True)
            self.level_view.set_mouse_mode(mkdd_widgets.MOUSE_MODE_ADDWP)
        elif option == "route_object":
            new_route = libbol.Route.new()
            forward, up, left = obj.rotation.get_vectors()

            new_point_1 = libbol.RoutePoint.new()
            new_point_1.position = obj.position + left * 250
            new_route.points.append(new_point_1)

            new_point_2 = libbol.RoutePoint.new()
            new_point_2.position = obj.position + left * -750
            new_route.points.append(new_point_2)
            self.action_ground_objects((new_point_1.position, new_point_2.position))

            self.level_file.routes.append(new_route)
            obj.pathid = len(self.level_file.routes) - 1
        elif option == "add_respawn":
            self.object_to_be_added = [libbol.JugemPoint.new(), -1, 0]
            self.pik_control.button_add_object.setChecked(True)
            self.level_view.set_mouse_mode(mkdd_widgets.MOUSE_MODE_ADDWP)


        self.leveldatatreeview.set_objects(self.level_file)

    @catch_exception
    def action_move_objects(self, deltax, deltay, deltaz):
        for i in range(len(self.level_view.selected_positions)):
            for j in range(len(self.level_view.selected_positions)):
                pos = self.level_view.selected_positions
                if i != j and pos[i] == pos[j]:
                    print("What the fuck")
        for pos in self.level_view.selected_positions:
            """obj.x += deltax
            obj.z += deltaz
            obj.x = round(obj.x, 6)
            obj.z = round(obj.z, 6)
            obj.position_x = obj.x
            obj.position_z = obj.z
            obj.offset_x = 0
            obj.offset_z = 0

            if self.editorconfig.getboolean("GroundObjectsWhenMoving") is True:
                if self.pikmin_gen_view.collision is not None:
                    y = self.pikmin_gen_view.collision.collide_ray_downwards(obj.x, obj.z)
                    obj.y = obj.position_y = round(y, 6)
                    obj.offset_y = 0"""
            pos.x += deltax
            pos.y += deltay
            pos.z += deltaz

        self.level_view.gizmo.move_to_average(self.level_view.selected_positions,
                                              self.level_view.selected_rotations)

        #if len(self.pikmin_gen_view.selected) == 1:
        #    obj = self.pikmin_gen_view.selected[0]
        #    self.pik_control.set_info(obj, obj.position, obj.rotation)

        #self.pikmin_gen_view.update()
        self.level_view.do_redraw()
        self.pik_control.update_info()
        self.set_has_unsaved_changes(True)


    @catch_exception
    def action_change_object_heights(self, deltay):
        for obj in self.pikmin_gen_view.selected:
            obj.y += deltay
            obj.y = round(obj.y, 6)
            obj.position_y = obj.y
            obj.offset_y = 0

        if len(self.pikmin_gen_view.selected) == 1:
            obj = self.pikmin_gen_view.selected[0]
            self.pik_control.set_info(obj, (obj.x, obj.y, obj.z), obj.get_rotation())

        #self.pikmin_gen_view.update()
        self.pikmin_gen_view.do_redraw()
        self.set_has_unsaved_changes(True)

    def keyPressEvent(self, event: QtGui.QKeyEvent):

        if event.key() == QtCore.Qt.Key_Escape:
            self.level_view.set_mouse_mode(mkdd_widgets.MOUSE_MODE_NONE)
            self.next_checkpoint_start_position = None
            self.pik_control.button_add_object.setChecked(False)
            #self.pik_control.button_move_object.setChecked(False)
            self.update_3d()

        if event.key() == QtCore.Qt.Key_Shift:
            self.level_view.shift_is_pressed = True
        elif event.key() == QtCore.Qt.Key_R:
            self.level_view.rotation_is_pressed = True
        elif event.key() == QtCore.Qt.Key_H:
            self.level_view.change_height_is_pressed = True

        if event.key() == QtCore.Qt.Key_W:
            self.level_view.MOVE_FORWARD = 1
        elif event.key() == QtCore.Qt.Key_S:
            self.level_view.MOVE_BACKWARD = 1
        elif event.key() == QtCore.Qt.Key_A:
            self.level_view.MOVE_LEFT = 1
        elif event.key() == QtCore.Qt.Key_D:
            self.level_view.MOVE_RIGHT = 1
        elif event.key() == QtCore.Qt.Key_Q:
            self.level_view.MOVE_UP = 1
        elif event.key() == QtCore.Qt.Key_E:
            self.level_view.MOVE_DOWN = 1

        if event.key() == QtCore.Qt.Key_Plus:
            self.level_view.zoom_in()
        elif event.key() == QtCore.Qt.Key_Minus:
            self.level_view.zoom_out()

    def keyReleaseEvent(self, event: QtGui.QKeyEvent):
        if event.key() == QtCore.Qt.Key_Shift:
            self.level_view.shift_is_pressed = False
        elif event.key() == QtCore.Qt.Key_R:
            self.level_view.rotation_is_pressed = False
        elif event.key() == QtCore.Qt.Key_H:
            self.level_view.change_height_is_pressed = False

        if event.key() == QtCore.Qt.Key_W:
            self.level_view.MOVE_FORWARD = 0
        elif event.key() == QtCore.Qt.Key_S:
            self.level_view.MOVE_BACKWARD = 0
        elif event.key() == QtCore.Qt.Key_A:
            self.level_view.MOVE_LEFT = 0
        elif event.key() == QtCore.Qt.Key_D:
            self.level_view.MOVE_RIGHT = 0
        elif event.key() == QtCore.Qt.Key_Q:
            self.level_view.MOVE_UP = 0
        elif event.key() == QtCore.Qt.Key_E:
            self.level_view.MOVE_DOWN = 0

    def reset_move_flags(self):
        self.level_view.MOVE_FORWARD = 0
        self.level_view.MOVE_BACKWARD = 0
        self.level_view.MOVE_LEFT = 0
        self.level_view.MOVE_RIGHT = 0
        self.level_view.MOVE_UP = 0
        self.level_view.MOVE_DOWN = 0
        self.level_view.shift_is_pressed = False
        self.level_view.rotation_is_pressed = False
        self.level_view.change_height_is_pressed = False

    def action_rotate_object(self, deltarotation):
        #obj.set_rotation((None, round(angle, 6), None))
        for rot in self.level_view.selected_rotations:
            if deltarotation.x != 0:
                rot.rotate_around_y(deltarotation.x)
            elif deltarotation.y != 0:
                rot.rotate_around_z(deltarotation.y)
            elif deltarotation.z != 0:
                rot.rotate_around_x(deltarotation.z)

        if self.rotation_mode.isChecked():
            middle = self.level_view.gizmo.position

            for position in self.level_view.selected_positions:
                diff = position - middle
                diff.y = 0.0

                length = diff.norm()
                if length > 0:
                    diff.normalize()
                    angle = atan2(diff.x, diff.z)
                    angle += deltarotation.y
                    position.x = middle.x + length * sin(angle)
                    position.z = middle.z + length * cos(angle)

        """
        if len(self.pikmin_gen_view.selected) == 1:
            obj = self.pikmin_gen_view.selected[0]
            self.pik_control.set_info(obj, obj.position, obj.rotation)
        """
        #self.pikmin_gen_view.update()
        self.level_view.do_redraw()
        self.set_has_unsaved_changes(True)
        self.pik_control.update_info()

    def action_ground_objects(self, objects=None):
        for pos in objects or self.level_view.selected_positions:
            if self.level_view.collision is None:
                return None
            height = self.level_view.collision.collide_ray_closest(pos.x, pos.z, pos.y)

            if height is not None:
                pos.y = height

        self.pik_control.update_info()
        self.level_view.gizmo.move_to_average(self.level_view.selected_positions,
                                              self.level_view.selected_rotations)
        self.set_has_unsaved_changes(True)
        self.level_view.do_redraw()

    def action_delete_objects(self):
        tobedeleted = []
        for obj in self.level_view.selected:
            if isinstance(obj, libbol.EnemyPoint):
                for group in self.level_file.enemypointgroups.groups:
                    if obj in group.points:
                        group.points.remove(obj)
                        break

            elif isinstance(obj, libbol.RoutePoint):
                for route in self.level_file.routes:
                    if obj in route.points:
                        route.points.remove(obj)
                        break

            elif isinstance(obj, libbol.Checkpoint):
                for group in self.level_file.checkpoints.groups:
                    if obj in group.points:
                        group.points.remove(obj)
                        break

            elif isinstance(obj, libbol.MapObject):
                self.level_file.objects.objects.remove(obj)
            elif isinstance(obj, libbol.KartStartPoint):
                self.level_file.kartpoints.positions.remove(obj)
            elif isinstance(obj, libbol.JugemPoint):
                self.level_file.respawnpoints.remove(obj)
            elif isinstance(obj, libbol.Area):
                self.level_file.areas.areas.remove(obj)
            elif isinstance(obj, libbol.Camera):
                self.level_file.cameras.remove(obj)
            elif isinstance(obj, libbol.CheckpointGroup):
                self.level_file.checkpoints.groups.remove(obj)
            elif isinstance(obj, libbol.EnemyPointGroup):
                self.level_file.enemypointgroups.groups.remove(obj)
            elif isinstance(obj, libbol.Route):
                self.level_file.routes.remove(obj)
            elif isinstance(obj, libbol.LightParam):
                self.level_file.lightparams.remove(obj)
            elif isinstance(obj, libbol.MGEntry):
                self.level_file.mgentries.remove(obj)
        self.level_view.selected = []
        self.level_view.selected_positions = []
        self.level_view.selected_rotations = []

        self.pik_control.reset_info()
        self.leveldatatreeview.set_objects(self.level_file)
        self.level_view.gizmo.hidden = True
        #self.pikmin_gen_view.update()
        self.level_view.do_redraw()
        self.set_has_unsaved_changes(True)

    def on_cut_action_triggered(self):
        self.on_copy_action_triggered()
        self.action_delete_objects()

    def on_copy_action_triggered(self):
        # Widgets are unpickleable, so they need to be temporarily stashed. This needs to be done
        # recursively, as top-level groups main contain points associated with widgets too.
        object_to_widget = {}
        pending = list(self.level_view.selected)
        while pending:
            obj = pending.pop(0)
            if hasattr(obj, 'widget'):
                object_to_widget[obj] = obj.widget
                obj.widget = None
            if hasattr(obj, '__dict__'):
                pending.extend(list(obj.__dict__.values()))
            if isinstance(obj, list):
                pending.extend(obj)
        try:
            # Effectively serialize the data.
            data = pickle.dumps(self.level_view.selected)
        finally:
            # Restore the widgets.
            for obj, widget in object_to_widget.items():
                obj.widget = widget

        mimedata = QtCore.QMimeData()
        mimedata.setData("application/mkdd-track-editor", QtCore.QByteArray(data))
        QtWidgets.QApplication.instance().clipboard().setMimeData(mimedata)

    def on_paste_action_triggered(self):
        mimedata = QtWidgets.QApplication.instance().clipboard().mimeData()
        data = bytes(mimedata.data("application/mkdd-track-editor"))
        if not data:
            return

        copied_objects = pickle.loads(data)
        if not copied_objects:
            return

        # If an tree item is selected, use it as a reference point for adding the objects that are
        # about to be pasted.
        selected_items = self.leveldatatreeview.selectedItems()
        selected_obj = selected_items[-1].bound_to if selected_items else None

        target_path = None
        target_checkpoint_group = None
        target_route = None

        if isinstance(selected_obj, libbol.EnemyPointGroup):
            target_path = selected_obj
        elif isinstance(selected_obj, libbol.EnemyPoint):
            for group in self.level_file.enemypointgroups.groups:
                if group.id == selected_obj.group:
                    target_path = group
                    break

        if isinstance(selected_obj, libbol.CheckpointGroup):
            target_checkpoint_group = selected_obj
        elif isinstance(selected_obj, libbol.Checkpoint):
            for group in self.level_file.checkpoints.groups:
                if selected_obj in group.points:
                    target_checkpoint_group = group
                    break

        if isinstance(selected_obj, libbol.Route):
            target_route = selected_obj
        elif isinstance(selected_obj, libbol.RoutePoint):
            for route in self.level_file.routes:
                if selected_obj in route.points:
                    target_route = route
                    break

        added = []

        for obj in copied_objects:
            # Group objects.
            if isinstance(obj, libbol.EnemyPointGroup):
                obj.id = self.level_file.enemypointgroups.new_group_id()
                self.level_file.enemypointgroups.groups.append(obj)
                for point in obj.points:
                    point.link = -1
                    point.group_id = obj.id
            elif isinstance(obj, libbol.CheckpointGroup):
                self.level_file.checkpoints.groups.append(obj)
            elif isinstance(obj, libbol.Route):
                self.level_file.routes.append(obj)

            # Objects in group objects.
            elif isinstance(obj, libbol.EnemyPoint):
                if target_path is None:
                    if not self.level_file.enemypointgroups.groups:
                        self.level_file.enemypointgroups.groups.append(libbol.EnemyPointGroup.new())
                    target_path = self.level_file.enemypointgroups.groups[-1]

                obj.group = target_path.id
                if not target_path.points:
                    obj.link = 0
                else:
                    obj.link = target_path.points[-1].link
                    if len(target_path.points) > 1:
                        target_path.points[-1].link = -1
                target_path.points.append(obj)

            elif isinstance(obj, libbol.Checkpoint):
                if target_checkpoint_group is None:
                    if not self.level_file.checkpoints.groups:
                        self.level_file.checkpoints.groups.append(libbol.CheckpointGroup.new())
                    target_checkpoint_group = self.level_file.checkpoints.groups[-1]

                target_checkpoint_group.points.append(obj)

            elif isinstance(obj, libbol.RoutePoint):
                if target_route is None:
                    if not self.level_file.routes:
                        self.level_file.routes.append(libbol.Route.new())
                    target_route = self.level_file.routes[-1]

                target_route.points.append(obj)

            # Autonomous objects.
            elif isinstance(obj, libbol.MapObject):
                self.level_file.objects.objects.append(obj)
            elif isinstance(obj, libbol.KartStartPoint):
                self.level_file.kartpoints.positions.append(obj)
            elif isinstance(obj, libbol.JugemPoint):
                max_respawn_id = -1
                for point in self.level_file.respawnpoints:
                    max_respawn_id = max(point.respawn_id, max_respawn_id)
                obj.respawn_id = max_respawn_id + 1
                self.level_file.respawnpoints.append(obj)
            elif isinstance(obj, libbol.Area):
                self.level_file.areas.areas.append(obj)
            elif isinstance(obj, libbol.Camera):
                self.level_file.cameras.append(obj)
            elif isinstance(obj, libbol.LightParam):
                self.level_file.lightparams.append(obj)
            elif isinstance(obj, libbol.MGEntry):
                self.level_file.mgentries.append(obj)
            else:
                continue

            added.append(obj)

        if not added:
            return

        self.set_has_unsaved_changes(True)
        self.leveldatatreeview.set_objects(self.level_file)

        self.select_tree_item_bound_to(added[-1])
        self.level_view.selected = added
        self.level_view.selected_positions = []
        self.level_view.selected_rotations = []
        for obj in added:
            if hasattr(obj, 'position'):
                self.level_view.selected_positions.append(obj.position)
            if hasattr(obj, 'start') and hasattr(obj, 'end'):
                self.level_view.selected_positions.append(obj.start)
                self.level_view.selected_positions.append(obj.end)
            if hasattr(obj, 'rotation'):
                self.level_view.selected_rotations.append(obj.rotation)

        self.update_3d()

    def update_3d(self):
        self.level_view.gizmo.move_to_average(self.level_view.selected_positions,
                                              self.level_view.selected_rotations)
        self.level_view.do_redraw()

    def select_from_3d_to_treeview(self):
        if self.level_file is not None:
            selected = self.level_view.selected
            if len(selected) == 1:
                currentobj = selected[0]
                item = None
                if isinstance(currentobj, libbol.EnemyPoint):
                    for i in range(self.leveldatatreeview.enemyroutes.childCount()):
                        child = self.leveldatatreeview.enemyroutes.child(i)
                        item = get_treeitem(child, currentobj)
                        if item is not None:
                            break

                elif isinstance(currentobj, libbol.Checkpoint):
                    for i in range(self.leveldatatreeview.checkpointgroups.childCount()):
                        child = self.leveldatatreeview.checkpointgroups.child(i)
                        item = get_treeitem(child, currentobj)

                        if item is not None:
                            break

                elif isinstance(currentobj, libbol.RoutePoint):
                    for i in range(self.leveldatatreeview.routes.childCount()):
                        child = self.leveldatatreeview.routes.child(i)
                        item = get_treeitem(child, currentobj)
                        if item is not None:
                            break

                elif isinstance(currentobj, libbol.MapObject):
                    item = get_treeitem(self.leveldatatreeview.objects, currentobj)
                elif isinstance(currentobj, libbol.Camera):
                    item = get_treeitem(self.leveldatatreeview.cameras, currentobj)
                elif isinstance(currentobj, libbol.Area):
                    item = get_treeitem(self.leveldatatreeview.areas, currentobj)
                elif isinstance(currentobj, libbol.JugemPoint):
                    item = get_treeitem(self.leveldatatreeview.respawnpoints, currentobj)
                elif isinstance(currentobj, libbol.KartStartPoint):
                    item = get_treeitem(self.leveldatatreeview.kartpoints, currentobj)

                # Temporarily suppress signals to prevent both checkpoints from
                # being selected when just one checkpoint is selected in 3D view.
                suppress_signal = False
                if (isinstance(currentobj, libbol.Checkpoint)
                    and (currentobj.start in self.level_view.selected_positions
                         or currentobj.end in self.level_view.selected_positions)):
                    suppress_signal = True

                if suppress_signal:
                    self.leveldatatreeview.blockSignals(True)

                if item is not None:
                    self.leveldatatreeview.setCurrentItem(item)

                if suppress_signal:
                    self.leveldatatreeview.blockSignals(False)

            #if nothing is selected and the currentitem is something that can be selected
            #clear out the buttons
            curr_item = self.leveldatatreeview.currentItem()
            if (not selected) and (curr_item is not None) and hasattr(curr_item, "bound_to"):
                bound_to_obj = curr_item.bound_to
                if bound_to_obj and hasattr(bound_to_obj, "position"):
                    self.pik_control.set_buttons(None)
    @catch_exception
    def action_update_info(self):
        if self.level_file is not None:
            selected = self.level_view.selected
            if len(selected) == 1:
                currentobj = selected[0]
                if isinstance(currentobj, Route):
                    objects = []
                    index = self.level_file.routes.index(currentobj)
                    for object in self.level_file.objects.objects:
                        if object.pathid == index:
                            objects.append(get_full_name(object.objectid))
                    for i, camera in enumerate(self.level_file.cameras):
                        if camera.route == index:
                            objects.append("Camera {0}".format(i))

                    self.pik_control.set_info(currentobj, self.update_3d, objects)
                else:
                    self.pik_control.set_info(currentobj, self.update_3d)

                self.pik_control.update_info()
            else:
                self.pik_control.reset_info("{0} objects selected".format(len(self.level_view.selected)))
                self.pik_control.set_objectlist(selected)

                # Without emitting any signal, programmatically update the currently selected item
                # in the tree view.
                with QtCore.QSignalBlocker(self.leveldatatreeview):
                    if selected:
                        # When there is more than one object selected, pick the last one.
                        self.select_tree_item_bound_to(selected[-1])
                    else:
                        # If no selection occurred, ensure that no tree item remains selected. This
                        # is relevant to ensure that non-pickable objects (such as the top-level
                        # items) do not remain selected when the user clicks on an empty space in
                        # the viewport.
                        for selected_item in self.leveldatatreeview.selectedItems():
                            selected_item.setSelected(False)

    @catch_exception
    def mapview_showcontextmenu(self, position):
        self.reset_move_flags()

        context_menu = QtWidgets.QMenu(self)
        action = QtGui.QAction("Copy Coordinates", self)
        action.triggered.connect(self.action_copy_coords_to_clipboard)
        context_menu.addAction(action)
        context_menu.exec(self.level_view.mapToGlobal(position))
        context_menu.destroy()

    def action_copy_coords_to_clipboard(self):
        if self.current_coordinates is not None:
            QtWidgets.QApplication.clipboard().setText(", ".join(
                str(x) for x in self.current_coordinates))

    def action_update_position(self, event, pos):
        self.current_coordinates = pos

        y_coord = f"{pos[1]:.2f}" if pos[1] is not None else "-"

        display_string = f"🖱️ ({pos[0]:.2f}, {y_coord}, {pos[2]:.2f})"

        selected = self.level_view.selected
        if len(selected) == 1 and hasattr(selected[0], "position"):

            obj_pos = selected[0].position
            display_string += f"   📦 ({obj_pos.x:.2f}, {obj_pos.y:.2f}, {obj_pos.z:.2f})"

            if self.level_view.collision is not None:
                height = self.level_view.collision.collide_ray_closest(obj_pos.x, obj_pos.z, obj_pos.y)
                if height is not None:
                    display_string += f"   📏 {obj_pos.y - height:.2f}"

        self.statusbar.showMessage(display_string)

    def dragEnterEvent(self, event):
        mime_data = event.mimeData()
        if mime_data.hasUrls():
            url = mime_data.urls()[0]
            filepath = url.toLocalFile()
            ext = os.path.splitext(filepath)[1].lower()
            if ext in (".bol", ".arc", ".bmd", ".bco"):
                event.acceptProposedAction()

    def dropEvent(self, event):
        mime_data = event.mimeData()
        if mime_data.hasUrls():
            url = mime_data.urls()[0]
            filepath = url.toLocalFile()
            ext = os.path.splitext(filepath)[1].lower()
            if ext in (".bol", ".arc"):
                self.button_load_level(filepath, update_config=False)
            elif ext == ".bco":
                self.load_optional_bco(filepath)
            elif ext == ".bmd":
                self.load_optional_bmd(filepath)

    def action_reverse_official_track(self):
        self.reverse_official_track()
        self.leveldatatreeview.set_objects(self.level_file)
        self.update_3d()

    def reverse_official_track(self):

        def similar_position(p, x, y, z):
            return abs(p.x - x) < 1.0 and abs(p.y - y) < 1.0 and abs(p.z - z) < 1.0

        def clone_map_object(obj):
            new_obj = libbol.MapObject.new()
            new_obj.position = obj.position.copy()
            new_obj.scale = obj.scale.copy()
            new_obj.rotation.set_vectors(*obj.rotation.get_vectors())
            new_obj.objectid = obj.objectid
            new_obj.pathid = obj.pathid
            new_obj.unk_28 = obj.unk_28
            new_obj.unk_2a = obj.unk_2a
            new_obj.presence_filter = obj.presence_filter
            new_obj.presence = obj.presence
            new_obj.unk_flag = obj.unk_flag
            new_obj.unk_2f = obj.unk_2f
            new_obj.userdata = list(obj.userdata)
            return new_obj

        def clone_map_area(area):
            new_area = libbol.Area.new()
            new_area.position = area.position.copy()
            new_area.scale = area.scale.copy()
            new_area.rotation.set_vectors(*area.rotation.get_vectors())
            new_area.check_flag = area.check_flag
            new_area.area_type = area.area_type
            new_area.camera_index = area.camera_index
            new_area.unk1 = area.unk1
            new_area.unk2 = area.unk2
            new_area.unkfixedpoint = area.unkfixedpoint
            new_area.unkshort = area.unkshort
            new_area.shadow_id = area.shadow_id
            new_area.lightparam_index = area.lightparam_index
            return new_area

        # Determine which course this is based on the position of the start point, which is assumed
        # unique (and in fact it is unique among the stock courses).

        class Course(object):
            LuigiCircuit = False
            LuigiCircuit2 = False
            PeachBeach = False
            BabyPark = False
            DryDryDesert = False
            MushroomBridge = False
            MarioCircuit = False
            DaisyCruiser = False
            WaluigiStadium = False
            SherbetLand = False
            MushroomCity = False
            YoshiCircuit = False
            DKMountain = False
            WarioColosseum = False
            DinoDinoJungle = False
            BowsersCastle = False
            RainbowRoad = False

        assert len(self.level_file.kartpoints.positions) == 1

        for point in self.level_file.kartpoints.positions:
            if similar_position(point.position, 9401, 3575, 16871):
                Course.LuigiCircuit = True
            elif similar_position(point.position, 9361, 3575, 16861):
                Course.LuigiCircuit2 = True
            elif similar_position(point.position, 9510, 3586, 3260):
                Course.PeachBeach = True
            elif similar_position(point.position, 310, 6000, 2826):
                Course.BabyPark = True
            elif similar_position(point.position, -25379, 5400, -5450):
                Course.DryDryDesert = True
            elif similar_position(point.position, 22461, 4000, 13912):
                Course.MushroomBridge = True
            elif similar_position(point.position, -15127, 1100, 2886):
                Course.MarioCircuit = True
            elif similar_position(point.position, 8353, 9000, 20):
                Course.DaisyCruiser = True
            elif similar_position(point.position, 3465, 997, -80):
                Course.WaluigiStadium = True
            elif similar_position(point.position, -5718, 1533, 1750):
                Course.SherbetLand = True
            elif similar_position(point.position, 16142, 5000, 1200):
                Course.MushroomCity = True
            elif similar_position(point.position, 4546, 12704, 34084):
                Course.YoshiCircuit = True
            elif similar_position(point.position, -14890, 4032, 243):
                Course.DKMountain = True
            elif similar_position(point.position, -13450, 22179, -979):
                Course.WarioColosseum = True
            elif similar_position(point.position, 13150, 8427, -6598):
                Course.DinoDinoJungle = True
            elif similar_position(point.position, 3624, 8109, 15533):
                Course.BowsersCastle = True
            elif similar_position(point.position, -15537, 58219, -36093):
                Course.RainbowRoad = True
            else:
                raise RuntimeError('Course not recognized.')

        # Checkpoints ------------------------------------------------------------------------------

        checkpointgroups = self.level_file.checkpoints.groups

        # Trivial case for a single group.
        if len(checkpointgroups) == 1:
            group = checkpointgroups[0]
            group.points = [group.points[0]] + list(reversed(group.points[1:]))
            for point in group.points:
                start = point.start
                point.start = point.end
                point.end = start

        # Special cases with more than one group.
        elif Course.YoshiCircuit:
            for group in checkpointgroups:
                for point in group.points:
                    start = point.start
                    point.start = point.end
                    point.end = start

            group_0_points = checkpointgroups[0].points
            group_2_points = checkpointgroups[2].points

            checkpointgroups[0].points = [group_0_points[0]] + list(reversed(group_2_points))
            checkpointgroups[1].points.reverse()
            checkpointgroups[2].points = list(reversed(group_0_points))[:-1]
            checkpointgroups[3].points.reverse()

            checkpointgroups[0].grouplink = 0
            checkpointgroups[0].prevgroup = [2, -1, -1, -1]
            checkpointgroups[0].nextgroup = [1, 3, -1, -1]
            checkpointgroups[1].grouplink = 1  # Not sure. Original has it.
            checkpointgroups[1].prevgroup = [0, -1, -1, -1]
            checkpointgroups[1].nextgroup = [2, -1, -1, -1]
            checkpointgroups[2].grouplink = 1  # Not sure. Original has it.
            checkpointgroups[2].prevgroup = [1, 3, -1, -1]
            checkpointgroups[2].nextgroup = [0, -1, -1, -1]
            checkpointgroups[3].grouplink = 32768  # Skippable.
            checkpointgroups[3].prevgroup = [0, -1, -1, -1]
            checkpointgroups[3].nextgroup = [2, -1, -1, -1]

        elif Course.MushroomCity:
            for group in checkpointgroups:
                for point in group.points:
                    start = point.start
                    point.start = point.end
                    point.end = start

            group_0_points = checkpointgroups[0].points
            group_1_points = checkpointgroups[1].points

            checkpointgroups[0].points = [group_0_points[0]] + list(reversed(group_1_points))
            checkpointgroups[1].points = list(reversed(group_0_points))[:-1]
            checkpointgroups[2].points.reverse()
            checkpointgroups[3].points.reverse()
            checkpointgroups[4].points.reverse()
            checkpointgroups[5].points.reverse()

            checkpointgroups[0].grouplink = 0
            checkpointgroups[0].prevgroup = [1, -1, -1, -1]
            checkpointgroups[0].nextgroup = [4, 5, -1, -1]
            checkpointgroups[1].grouplink = 0
            checkpointgroups[1].prevgroup = [2, 3, -1, -1]
            checkpointgroups[1].nextgroup = [0, -1, -1, -1]
            checkpointgroups[2].grouplink = 32768  # Skippable.
            checkpointgroups[2].prevgroup = [4, 5, -1, -1]
            checkpointgroups[2].nextgroup = [1, -1, -1, -1]
            checkpointgroups[3].grouplink = 1  # Not sure. Original has it.
            checkpointgroups[3].prevgroup = [4, 5, -1, -1]
            checkpointgroups[3].nextgroup = [1, -1, -1, -1]
            checkpointgroups[4].grouplink = 1  # Not sure. Original has it.
            checkpointgroups[4].prevgroup = [0, -1, -1, -1]
            checkpointgroups[4].nextgroup = [2, 3, -1, -1]
            checkpointgroups[5].grouplink = 32768  # Skippable.
            checkpointgroups[5].prevgroup = [0, -1, -1, -1]
            checkpointgroups[5].nextgroup = [2, 3, -1, -1]

        elif Course.WarioColosseum:
            for group in checkpointgroups:
                for point in group.points:
                    start = point.start
                    point.start = point.end
                    point.end = start

            group_0_points = checkpointgroups[0].points
            group_1_points = checkpointgroups[1].points

            checkpointgroups[0].points = [group_0_points[0]] + list(reversed(group_1_points))
            checkpointgroups[1].points = list(reversed(group_0_points))[:-1]

            checkpointgroups[0].grouplink = 0
            checkpointgroups[0].prevgroup = [1, -1, -1, -1]
            checkpointgroups[0].nextgroup = [1, -1, -1, -1]
            checkpointgroups[1].grouplink = 0
            checkpointgroups[1].prevgroup = [0, -1, -1, -1]
            checkpointgroups[1].nextgroup = [0, -1, -1, -1]

        elif checkpointgroups:
            checkpointgroups_str = ', '.join(tuple(str(len(g.points)) for g in checkpointgroups))
            open_error_dialog(
                'Unrecognized number of checkpoints in checkpoint groups ({}).\n\n'.format(
                    checkpointgroups_str) +
                'Checkpoint groups have not been reversed: the result would likely be incoherent.',
                self)

        # Kart Start Points ------------------------------------------------------------------------

        for point in self.level_file.kartpoints.positions:
            # Kart start points are merely rotated by 180 degrees.
            point.rotation.rotate_around_z(pi)

            POLE_LEFT = 0
            POLE_RIGHT = 1

            # Each course has a finish line of a different width. The offset has been determined
            # empirically to a value that looks good, so that the karts do not step over the line.
            if Course.LuigiCircuit:
                offset = 1080
                point.poleposition = POLE_RIGHT
            elif Course.LuigiCircuit2:
                offset = 1070
                point.poleposition = POLE_RIGHT
            elif Course.PeachBeach:
                offset = 1015
                point.poleposition = POLE_LEFT
            elif Course.BabyPark:
                offset = 1150
                point.poleposition = POLE_LEFT
            elif Course.DryDryDesert:
                offset = 1160
                point.poleposition = POLE_LEFT
            elif Course.MushroomBridge:
                offset = 965
                point.poleposition = POLE_RIGHT
            elif Course.MarioCircuit:
                offset = 1200
                point.poleposition = POLE_RIGHT
            elif Course.DaisyCruiser:
                offset = 1410
                point.poleposition = POLE_RIGHT
            elif Course.WaluigiStadium:
                offset = 1070
                point.poleposition = POLE_LEFT
            elif Course.SherbetLand:
                offset = 1050
                point.poleposition = POLE_LEFT
            elif Course.MushroomCity:
                offset = 1210
                point.poleposition = POLE_RIGHT
            elif Course.YoshiCircuit:
                offset = 1055
                point.poleposition = POLE_LEFT
            elif Course.DKMountain:
                offset = 965
                point.poleposition = POLE_RIGHT
            elif Course.WarioColosseum:
                offset = 1005
                point.poleposition = POLE_RIGHT
            elif Course.DinoDinoJungle:
                offset = 1005
                point.poleposition = POLE_RIGHT
            elif Course.BowsersCastle:
                offset = 1065
                point.poleposition = POLE_RIGHT
            elif Course.RainbowRoad:
                offset = 1110
                point.poleposition = POLE_LEFT

            forward, _up, _left = point.rotation.get_vectors()
            point.position -= forward * offset

        # Start Line Camera Position ---------------------------------------------------------------

        # This is an automatic attempt to make cameras look at the karts at the start of the race.
        intro_cameras = set()
        for camera in self.level_file.cameras:
            if camera.startcamera == 1:
                break
        assert camera.startcamera == 1
        intro_cameras.add(camera)
        while camera.nextcam != -1:
            camera = self.level_file.cameras[camera.nextcam]
            intro_cameras.add(camera)
        karts_start_point = self.level_file.kartpoints.positions[0]
        karts_start_position = karts_start_point.position
        karts_start_direction, _up, _left = karts_start_point.rotation.get_vectors()
        karts_start_direction = karts_start_direction.unit()
        karts_middle_position = karts_start_position - (karts_start_direction * 400)
        camera.position2 = karts_middle_position
        if camera.camtype == 4:  # Only end point is looked at.
            camera.position3.x = camera.position2.x
            camera.position3.y = camera.position2.y
            camera.position3.z = camera.position2.z

        # Special tweaks for some tracks.
        camera_route = self.level_file.routes[camera.route]
        for point in camera_route.points:
            if Course.LuigiCircuit or Course.LuigiCircuit2:
                point.position.z -= 4000
            elif Course.PeachBeach:
                point.position.x -= 600
                point.position.z += 900
            elif Course.BabyPark:
                point.position.z -= 1000
            elif Course.DryDryDesert:
                point.position.z += 2000
            elif Course.MushroomBridge:
                point.position.x += 4000
                point.position.y += 2000
            elif Course.MarioCircuit:
                point.position.y += 200
                point.position.z -= 3000
            elif Course.WaluigiStadium:
                point.position.x -= 2500
                point.position.y += 500
            elif Course.YoshiCircuit:
                point.position.x -= 1000
                point.position.y += 500
                point.position.z += 2500
            elif Course.DKMountain:
                point.position.y += 500
                point.position.z += 2500
            elif Course.WarioColosseum:
                point.position.x += 1000
                point.position.z += 3000
        if Course.DaisyCruiser:
            # Camera type is 6 (static camera that only rotates).
            camera.position.x -= 3000
            camera.position.y += 200
            camera.position.z += 1000
        elif Course.BowsersCastle:
            # Camera type is 6 (static camera that only rotates).
            camera.position.x -= 200
            camera.position.y += 500
            camera.position.z -= 2000

        # Area Camera Routes -----------------------------------------------------------------------

        # Post-race cameras that follow a route need to be reversed, or else it doesn't feel natural
        # when karts are framed while the camera moves far away.
        visited_cameras = set()
        for i, area in enumerate(self.level_file.areas.areas):
            if area.camera_index < 0:
                continue
            camera = self.level_file.cameras[area.camera_index]
            if camera in visited_cameras:
                continue
            visited_cameras.add(camera)
            assert camera not in intro_cameras, 'Area camera not expected in the intro sequence'
            if camera.route >= 0:
                route = self.level_file.routes[camera.route]
                route.points.reverse()
            # What about swapping intro-outro zoom levels? What about swapping look-at positions?
            # Some of these cameras still feel slightly unnatural, or end up pointing to the kart
            # that is behind a hill, ...but improving these require manual adjustments to each of
            # cameras. Testing these changes is also cumbersome.

        # Enemy Points -----------------------------------------------------------------------------

        # In Mushroom Bridge, it's been noticed that some intermediate enemy points have a link
        # value that is not -1. This appears to be an oversight by the original makers. This
        # algorithm requires that all intermediate points have no link value.
        for group in self.level_file.enemypointgroups.groups:
            for point in group.points[1:-1]:
                point.link = -1

        for group in self.level_file.enemypointgroups.groups:
            # As documented in http://wiki.tockdom.com/wiki/BOL_(File_Format), the first point in
            # the group stores whether the group can be followed by enemies and items, or only by
            # items. This value needs to be preserved.
            # NOTE: It seems only the lower byte is relevant. The higher byte is something else.
            ONLY_ITEMS_FOLLOW = 0x0001
            only_items_follow = group.points[0].groupsetting & 0x00FF == ONLY_ITEMS_FOLLOW

            # The rest of the settings will be reset. At this point, we (the community) don't yet
            # fully understand the purpose of these bytes. To avoid erratic behavior, all bytes will
            # be discarded. This implies that the AI's skills are slightly depleted. For example,
            # the AI won't know when to start drifting on sharp curves.
            for point in group.points:
                point.pointsetting = 0
                point.groupsetting = 0
                point.pointsetting2 = 0
                point.unk1 = 0
                point.unk2 = 0

            group.points.reverse()

            if only_items_follow:
                group.points[0].groupsetting |= ONLY_ITEMS_FOLLOW

        # After reversing, the former last group needs to become the new first group. This
        # guarantees that the start of the course remains aligned with the first enemy point of the
        # first group.
        former_first_group = self.level_file.enemypointgroups.groups[0]
        new_first_group = None
        for new_first_group in self.level_file.enemypointgroups.groups:
            if former_first_group.points[-1].link == new_first_group.points[0].link:
                break
        if former_first_group is not new_first_group:
            new_first_group_index = self.level_file.enemypointgroups.groups.index(new_first_group)
            self.level_file.enemypointgroups.groups[new_first_group_index] = former_first_group
            self.level_file.enemypointgroups.groups[0] = new_first_group

        # To keep enemy point groups in a sensible order, the links will be renamed in an ascending
        # order. This makes the data more human-readable, but it also appears to be a requirement;
        # the AI might misbehave if the links are in descending order.
        first_segment = None
        all_segments = set()
        for group in self.level_file.enemypointgroups.groups:
            # Convert to string. It will be replaced with the new integer value.
            group.points[0].link = str(group.points[0].link)
            group.points[-1].link = str(group.points[-1].link)
            segment = (group.points[0].link, group.points[-1].link)
            if first_segment is None:
                first_segment = segment
            all_segments.add(segment)
        visited_segments = collections.OrderedDict()
        pending_segments = [first_segment]
        while pending_segments:
            pending_segment = pending_segments[0]
            del pending_segments[0]
            visited_segments[pending_segment] = True
            for segment in all_segments:
                if segment not in visited_segments:
                    if pending_segment[1] == segment[0]:
                        pending_segments.append(segment)
        assert len(all_segments) == len(visited_segments)
        new_links_names = {}
        for segment in visited_segments:
            if segment[0] not in new_links_names:
                new_links_names[segment[0]] = len(new_links_names)
            if segment[1] not in new_links_names:
                new_links_names[segment[1]] = len(new_links_names)
        for point in self.level_file.enemypointgroups.points():
            if point.link in new_links_names:
                point.link = new_links_names[point.link]
        # Note that the groups are being sorted twice, to deprioritize items-only groups.
        self.level_file.enemypointgroups.groups.sort(key=lambda group: group.points[0].groupsetting)
        self.level_file.enemypointgroups.groups.sort(key=lambda group: group.points[0].link)

        # Finally, rebuild IDs and indices depending on the position of the group in the list.
        self.level_file.enemypointgroups._group_ids = {}
        for i, group in enumerate(self.level_file.enemypointgroups.groups):
            group.id = i
            self.level_file.enemypointgroups._group_ids[i] = group
            for point in group.points:
                point.group = i

        # Respawn Points ---------------------------------------------------------------------------

        for respawn_point in self.level_file.respawnpoints:
            respawn_point.rotation.rotate_around_z(pi)

            # Find the two closest enemy points; the index [of the one that is ahead in the course]
            # will be used for the next enemy point field in the respawn point. Using the greater of
            # the two indices guarantees that the enemy point is ahead of the respawn point, or else
            # the AI would attempt to drive backwards (and probably fall over again and again).
            index_and_distance = []
            index_offset = 0
            for group in self.level_file.enemypointgroups.groups:
                for i, point in enumerate(group.points):
                    distance = (point.position - respawn_point.position).norm()
                    index_and_distance.append((index_offset + i, distance))
                index_offset += len(group.points)
            index_and_distance.sort(key=lambda entry: entry[1])
            next_enemy_point = max(index_and_distance[0][0], index_and_distance[1][0])
            respawn_point.unk1 = next_enemy_point

            # Clear the previous checkpoint, as it's no longer accurate.

        # Other Special Cases ----------------------------------------------------------------------

        if Course.LuigiCircuit2:
            # Enemy points at the entrance of the boost pad need to be reduced, so that karts don't
            # take a wrong turn in the last second (they wouldn't struggle to get in track since
            # there are concrete walls). This only affects the fast Luigi Circuit ("2"), as in the
            # 50cc version there are walls that stop karts from taking wrong turns.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, 7233, 3252, 9388):
                    point.position.x = 7899.375
                    point.position.z = 10968.89
                    point.scale = 600
                elif similar_position(point.position, -11457, 249, -20429):
                    point.position.x = -11005.607
                    point.position.z = -19089.607
                    point.position.y = 48.403
                    point.scale = 600

            # Similarly, some checkpoints need to be tweaked, or else the lap completion progress is
            # restarted if karts take the wrong turn by accident. Things can still go wrong if the
            # player proceeds to drive in the wrong direction for a long time, but at least
            # accidents are prevented.
            for group in self.level_file.checkpoints.groups:
                for point in group.points:
                    if similar_position(point.end, 7007, 3627, 11256):
                        point.end.x = -166.498
                        point.end.y = 3627.178
                        point.end.z = 13013.142
                    elif similar_position(point.end, 7058, 3792, 11778):
                        point.end.x = -66.188
                        point.end.y = 3792.661
                        point.end.z = 13437.938

        elif Course.PeachBeach:
            # In Peach Beach, the respan points around the pipe shortcut didn't need to be rotated
            # 180 degrees. They need to be rotated back.
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, 13394, 4863, 26497):
                    point.rotation.rotate_around_z(pi)
                elif similar_position(point.position, 13404, 1985, 26490):
                    point.rotation.rotate_around_z(pi)
            # And a few others that need to be slightly tweaked.
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, 3530, 810, -25778):
                    point.position.x = 4958.111
                    point.position.z = -25683.032
                elif similar_position(point.position, -4813, 810, -16010):
                    point.rotation.rotate_around_z(-0.5)
                elif similar_position(point.position, 665, 810, 14065):
                    point.rotation.rotate_around_z(-0.3)
                elif similar_position(point.position, -8297, 968, 20237):
                    point.rotation.rotate_around_z(0.9)
                elif similar_position(point.position, 2215, 1990, 26503):
                    point.rotation.rotate_around_z(0.4)
                elif similar_position(point.position, 8758, 2362, 23014):
                    point.rotation.rotate_around_z(0.5)

            # Enemy points near the restored alternate path ned to be tweaked.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, -15500, 593, -3500):
                    point.position.x = -15063.798
                elif similar_position(point.position, -14387, 586, -3324):
                    point.position.x = -14492.327
            # Also the item box needs to be tweaked.
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, -13214, 1108, 8701):
                    obj.position.x -= 1200
                    obj.position.z = -2819.96
                elif similar_position(obj.position, -13793, 1108, 8698):
                    obj.position.x -= 1200
                    obj.position.z = -2819.96

        elif Course.DryDryDesert:
            for point in self.level_file.respawnpoints:
                # In Dry Dry Desert, the respawn point at the sinkhole needs to be moved to the
                # other side of the sinkhole.
                if similar_position(point.position, 17745, 5034, -528):
                    next_enemy_point = 27
                    point.unk1 = next_enemy_point
                    point.position.x = 18493.176
                    point.position.z = -15267.074
                # Some respawn points needs to be reoriented slightly.
                elif similar_position(point.position, 17750, 5809, -25813):
                    point.rotation.rotate_around_z(0.6)
                elif similar_position(point.position, -3291, 4163, -26391):
                    point.rotation.rotate_around_z(1.0)
                elif similar_position(point.position, -21375, 5405, -27431):
                    point.rotation.rotate_around_z(0.5)
                # The automatic attempt to determine the next enemy point failed for one respawn
                # point.
                elif similar_position(point.position, 16245, 5684, 11202):
                    next_enemy_point = 21
                    point.unk1 = next_enemy_point
            # The last item boxes are not too useful in the last lap. They will be moved back, to
            # give time to players to use the item.
            for obj in self.level_file.objects.objects:
                a = type(obj.position)(-25809.5, 5424.471, -22410.2)
                b = type(obj.position)(-24233.2, 5417.722, -22045.0)
                if similar_position(obj.position, -26163, 5440, -12651):
                    obj.position = a
                elif similar_position(obj.position, -25657, 5442, -12651):
                    obj.position = a + (b - a) / 3.0
                elif similar_position(obj.position, -25151, 5444, -12651):
                    obj.position = a + (b - a) / 3.0 * 2.0
                elif similar_position(obj.position, -24658, 5445, -12651):
                    obj.position = b

        elif Course.MushroomBridge:
            # In Mushroom Bridge, the respawn points around the pipe shortcut didn't need to be
            # rotated 180 degrees. They need to be rotated back.
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, 36796, 4441, 8239):
                    point.rotation.rotate_around_z(pi)

            # The automatic attempt to set the next enemy point didn't work in several respawn
            # points (the other side of the lake happens to be closer).
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, 1997, 4000.0, 12027):
                    point.unk1 = 4
                elif similar_position(point.position, 11021, 4000, 12027):
                    point.unk1 = 3
                elif similar_position(point.position, 24430, 4000, 12000):
                    point.unk1 = 0

            # The first two enemy points need to be tweaked, and scaled, or else CPU karts make a
            # very awkward turn at the start of the race as if they were chasing a rabbit or
            # something.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, 21800, 4000, 12130):
                    point.scale = 2500
                elif similar_position(point.position, 20860, 4000, 12127):
                    point.position.x = 18920.894
                    point.scale = 1400

            # Two more enemy points need to be tweaked, or else CPU karts can end up in the guarded
            # lanes if hit by shell, struck by lighning, et cetera.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, 7233, 2789, 3312):
                    point.position.x = 6976.384
                    point.position.z = 2670.556
                elif similar_position(point.position, 9587, 2999, 3208):
                    point.position.x = 9415.858
                    point.position.z = 2266.76

        elif Course.MarioCircuit:
            # Last item boxes are not too useful in the last lap. They will be moved a few curves
            # ahead.
            for obj in self.level_file.objects.objects:
                a = type(obj.position)(-4969.5, 1100, 18378.6)
                b = type(obj.position)(-3498.1, 1100, 18847.9)
                if similar_position(obj.position, -15943, 1100, 15241):
                    obj.position = a
                elif similar_position(obj.position, -15435, 1100, 15205):
                    obj.position = a + (b - a) / 4.0
                elif similar_position(obj.position, -14927, 1100, 15165):
                    obj.position = a + (b - a) / 4.0 * 2.0
                elif similar_position(obj.position, -14406, 1100, 15125):
                    obj.position = a + (b - a) / 4.0 * 3.0
                elif similar_position(obj.position, -13932, 1100, 15081):
                    obj.position = b

        elif Course.DaisyCruiser:
            # In Daisy Cruiser, when AI karts fall through the sinkhole, they don't know how to use
            # the cannon to get out. A new water zone (Roadtype_0x0F00_0x00000101) will be added in
            # the sinkhole to address this.
            # (Even if it was possible to work out a solution where karts still use the cannon to
            # get out, the penalty for falling in the hole would be too great.)
            # Remove the old enemy point group that was located in the basement.
            del self.level_file.enemypointgroups.groups[2]
            # Reassign group IDs.
            self.level_file.enemypointgroups._group_ids = {}
            for i, group in enumerate(self.level_file.enemypointgroups.groups):
                group.id = i
                self.level_file.enemypointgroups._group_ids[i] = group
                for point in group.points:
                    point.group = i
            # The respawn point associated with the newly added water zone (0x0F00) needs to be
            # re-placed.
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, 19395, 7995, -4306):
                    point.position.x = -2734.657
                    point.position.y = 6300
                    point.position.z = 3572.106
                    next_enemy_point = 29
                    point.unk1 = next_enemy_point
                    point.unk3 = 16
                    point.rotation.rotate_around_z(-pi / 2)
            # The swimming pool needs to be cloned, as the basement is not full of water. A new
            # water zone  is defined in the BCO file.
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, -24987, 8210, -2000):
                    new_pool = clone_map_object(obj)
                    new_pool.position.x = 2780.219
                    new_pool.position.y = 6100
                    new_pool.position.z = 3448.066
                    self.level_file.objects.objects.append(new_pool)

                    # A splash object is created as well. Without this, the splash effect was not
                    # working, which is interesting, considering that the other swiming pool
                    # (0x0F01_0x000001FF) did not require this splash object for some reason. The
                    # index of this splash object (1) matches the last byte in the material label of
                    # the new pool.
                    splash_obj = libbol.MapObject.new()
                    splash_obj.presence_filter = 143
                    splash_obj.presence = 3  # Present in both levels of detail.
                    splash_obj.objectid = 4209  # GeoSplash
                    splash_obj.position.x = new_pool.position.x
                    splash_obj.position.y = new_pool.position.y
                    splash_obj.position.z = new_pool.position.z
                    splash_obj.userdata[0] = 1  # Index.
                    splash_obj.userdata[1] = 2  # Type of splash.
                    self.level_file.objects.objects.append(splash_obj)

            # A respawn point (by the swimming pool) needs its next enemy point set, its preceding
            # checkpoint index set, and its orientation tweaked.
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, -27779, 8499, 2037):
                    next_enemy_point = 68
                    point.unk1 = next_enemy_point
                    point.unk3 = 29
                    point.rotation.rotate_around_z(0.8)

            # Clone some item boxes near the swimming pool (the last item boxes are too close to the
            # finish line).
            offset_x = -58488
            offset_y = 1250
            offset_z = 2000
            offset_pathid = len(self.level_file.routes) - 25
            clone_object_paths = []
            for i, route in enumerate(self.level_file.routes):
                if 25 <= i <= 29:
                    assert len(route.points) == 2
                    route_point_0 = type(route.points[0]).new()
                    route_point_0.position += route.points[0].position
                    route_point_0.position.x += offset_x
                    route_point_0.position.y += offset_y
                    route_point_0.position.z += offset_z
                    route_point_1 = type(route.points[1]).new()
                    route_point_1.position += route.points[1].position
                    route_point_1.position.x += offset_x
                    route_point_1.position.y += offset_y
                    route_point_1.position.z += offset_z
                    route = type(route)()
                    route.points = [route_point_0, route_point_1]
                    clone_object_paths.append(route)
            assert len(clone_object_paths) == 5
            self.level_file.routes.extend(clone_object_paths)
            clone_item_boxes = []
            for obj in self.level_file.objects.objects:
                if 25 <= obj.pathid <= 29:
                    obj = clone_map_object(obj)
                    obj.position.x += offset_x
                    obj.position.y += offset_y
                    obj.position.z += offset_z
                    obj.pathid += offset_pathid
                    clone_item_boxes.append(obj)
            assert len(clone_item_boxes) == 10
            self.level_file.objects.objects.extend(clone_item_boxes)

            # Last items will be moved further from the finish line as well.
            offset_x = -5600
            for i, route in enumerate(self.level_file.routes):
                if 11 <= i <= 15:
                    assert len(route.points) == 2
                    route.points[0].position.x += offset_x
                    route.points[1].position.x += offset_x
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, -10700, 9500, -6325):
                    obj.position.x += offset_x
                elif similar_position(obj.position, -10700, 9500, -6075):
                    obj.position.x += offset_x
                elif similar_position(obj.position, -10700, 9500, -5825):
                    obj.position.x += offset_x
                elif similar_position(obj.position, -10700, 9500, -5575):
                    obj.position.x += offset_x
                elif similar_position(obj.position, -10700, 9500, -5325):
                    obj.position.x += offset_x
                elif similar_position(obj.position, -10468, 9300, -6071):
                    obj.position.x += offset_x
                elif similar_position(obj.position, -10468, 9300, -5661):
                    obj.position.x += offset_x
                elif similar_position(obj.position, -10468, 9300, -5251):
                    obj.position.x += offset_x
                elif similar_position(obj.position, -10468, 9300, -4841):
                    obj.position.x += offset_x
                elif similar_position(obj.position, -10468, 9300, -4431):
                    obj.position.x += offset_x

            # Space out some enemy points as well, or else karts may follow the wrong one. This is
            # in theory the same issue thatw as first discovered in Mushroom City in the main
            # junction.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, -6716, 6499, -3619):
                    point.position.x = -6373.894
                    point.position.z = -2849.078
                elif similar_position(point.position, -6398, 6499, -4426):
                    point.position.x = -6719.29
                    point.position.z = -4641.356

            # Move these enemy points further away from the sinkhole.
            self.level_file.enemypointgroups.groups[1].points[7].position.x -= 400
            self.level_file.enemypointgroups.groups[1].points[8].position.x -= 300
            self.level_file.enemypointgroups.groups[1].points[9].position.x += 500
            self.level_file.enemypointgroups.groups[1].points[10].position.x += 500
            self.level_file.enemypointgroups.groups[1].points[10].position.z += 100
            self.level_file.enemypointgroups.groups[1].points[12].position.z -= 50

        elif Course.WaluigiStadium:
            # In Waluigi Stadium, a number of item boxes and fire balls are now too high for reach,
            # as in the reverse mode karts don't get that high up. These objects will be moved
            # downwards slightly.
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, 12879, 3079, -11):
                    obj.position.y -= 425
                elif similar_position(obj.position, 12867, 3242, -19):
                    obj.position.y -= 425
                elif similar_position(obj.position, 12872, 3242, -19):
                    obj.position.y -= 425
                elif similar_position(obj.position, -8025, 3114, -4947):
                    obj.position.y -= 800
                elif similar_position(obj.position, -8123, 3220, -4953):
                    obj.position.y -= 800
                elif similar_position(obj.position, -8118, 3220, -4953):
                    obj.position.y -= 800

            for point in self.level_file.respawnpoints:
                # The automatic attempt to select next enemy point failed in one respawn point.
                if similar_position(point.position, -10484, 1588, -4949):
                    next_enemy_point = 41
                    point.unk1 = next_enemy_point
                # The respawn points around the three little slopes needs to be moved to the now
                # last slope.
                elif similar_position(point.position, 579, 1154, -10444):
                    point.position.x = -4388.463
                    next_enemy_point = 52
                    point.unk1 = next_enemy_point

            # Enemy points at the deepened segment are adjusted in height.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, 12947, 1242, -6231):
                    point.position.y = 1035.275
                elif similar_position(point.position, 12877, 686, -2924):
                    point.position.y = -146.868
                elif similar_position(point.position, 12947, 1242, -6231):
                    point.position.y = 959.507

        elif Course.SherbetLand:
            # Cosmetic tweaks for the one respawn point.
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, 7719, 1176, -17237):
                    point.rotation.rotate_around_z(0.5)
            # Move the last item boxes, so that the now last curve can be fun.
            for obj in self.level_file.objects.objects:
                a = type(obj.position)(-155.3, 1184, -18211.2)
                b = type(obj.position)(1506.2, 1184, -16736.7)
                if similar_position(obj.position, -3191, 1315, -7695):
                    obj.position = a
                    obj.userdata[1] = 3  # Always double prize
                elif similar_position(obj.position, -2889, 1326, -7221):
                    obj.position = a + (b - a) / 3.0
                    obj.userdata[1] = 0  # Single or double prize
                elif similar_position(obj.position, -2590, 1337, -6771):
                    obj.position = a + (b - a) / 3.0 * 2.0
                    obj.userdata[1] = 1  # Always single prize
                elif similar_position(obj.position, -2321, 1346, -6352):
                    obj.position = b
                    obj.userdata[1] = 1  # Always single prize

        elif Course.MushroomCity:
            # A number of respawn points need to be tweaked.
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, -6142, 5000, -889):
                    next_enemy_point = 3
                    point.unk1 = next_enemy_point
                elif similar_position(point.position, 17644, 5000, 1188):
                    next_enemy_point = 0
                    point.unk1 = next_enemy_point
                elif similar_position(point.position, 17644, 5000, 1188):
                    next_enemy_point = 0
                    point.unk1 = next_enemy_point
                elif similar_position(point.position, 38494, 4000, 13204):
                    point.rotation.rotate_around_z(0.8)
                elif similar_position(point.position, 7497, 4000, 13296):
                    point.rotation.rotate_around_z(pi / 2.0)
                elif similar_position(point.position, -6156, 5000, -911):
                    next_enemy_point = 3
                    point.unk1 = next_enemy_point
                elif similar_position(point.position, 3964, 5541, -900):
                    next_enemy_point = 22
                    point.unk1 = next_enemy_point
            # Enemy points in the main junction need to be spaced out, or else AI karts may end up
            # following the enemy route that is meant for human karts (and items). There is no real
            # explanation for this, but spacing them out seems to be a workaround.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, 8013, 4000, 2640):
                    point.position.x = 8049.321
                    point.position.z = 2960.635
                elif similar_position(point.position, 9537, 4020, 1159):
                    point.position.x = 9069.965
                    point.position.z = 1537.109
                elif similar_position(point.position, 9500, 4000, 750):
                    point.position.x = 10331.2
                    point.position.z = 622.4
                elif similar_position(point.position, 9539, 4000, -731):
                    point.position.x = 9824.571
                    point.position.z = -838.578
            # Move the last item boxes, so that the now last curve can be fun.
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, 29307, 5000, 2789):
                    obj.position.x = 31300
                    obj.position.y -= 1000
                    obj.position.z += 9750
                elif similar_position(obj.position, 29304, 5000, 3222):
                    obj.position.x = 31300
                    obj.position.y -= 1000
                    obj.position.z += 9750
                elif similar_position(obj.position, 29304, 5000, 3660):
                    obj.position.x = 31300
                    obj.position.y -= 1000
                    obj.position.z += 9750
                elif similar_position(obj.position, 29310, 5000, 4053):
                    obj.position.x = 31300
                    obj.position.y -= 1000
                    obj.position.z += 9750

        elif Course.YoshiCircuit:
            # Cosmetic tweaks for respawn points.
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, 3018, 13860, -13285):
                    point.rotation.rotate_around_z(-1.0)
                elif similar_position(point.position, 8601, 12936, -3799):
                    point.rotation.rotate_around_z(0.4)
            # Move the last item boxes, so that the now last curve can be fun.
            for obj in self.level_file.objects.objects:
                a = type(obj.position)(-1951.3, 13000, 20239.401)
                b = type(obj.position)(-938.9, 13005, 19263.9)
                if similar_position(obj.position, -7804, 12716, 29073):
                    obj.position = b
                elif similar_position(obj.position, -7275, 12716, 29000):
                    obj.position = a + (b - a) / 3.0 * 2.0
                elif similar_position(obj.position, -6750, 12716, 28928):
                    obj.position = a + (b - a) / 3.0
                elif similar_position(obj.position, -6222, 12716, 28839):
                    obj.position = a
            # Add a new respawn point for the new pipe shortcut in the alternate path.
            new_respawn_point = libbol.JugemPoint.new()
            new_respawn_point.position.x = 2120.87
            new_respawn_point.position.y = 15475
            new_respawn_point.position.z = -10251.5
            forward, up, left = new_respawn_point.rotation.get_vectors()
            forward.x = -0.1365
            forward.y = 0.0
            forward.z = -0.9906
            up.x = 0.0
            up.y = 1.0
            up.z = 0.0
            left.x = -0.9906
            left.y = 0.0
            left.z = 0.1365
            new_respawn_point.rotation.set_vectors(forward, up, left)
            new_respawn_point.respawn_id = 7
            next_enemy_point = 43
            new_respawn_point.unk1 = next_enemy_point
            new_respawn_point.unk2 = -1
            new_respawn_point.unk3 = -1
            self.level_file.respawnpoints.append(new_respawn_point)

            # The respawn point assigned to the shortcut point needs to be moved further back, to
            # penalize a failed shortcut.
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, -9107, 13031, 15855):
                    point.position.x = -10527.408
                    point.position.z = 9823.485
                    point.rotation.rotate_around_z(pi + 0.15)
                    point.unk1 = 84  # Next enemy point.
                # Near this pond there is another slightly misplaced respawn point that can do with
                # some cosmetic tweaks.
                elif similar_position(point.position, -10674, 13057, 10226):
                    point.position.x = -9147.239
                    point.position.z = 8964.823

            # New areas (type 0) for shadow lighting inside the pipes are required.
            new_areas = []
            for area in self.level_file.areas.areas:
                if similar_position(area.position, 2164, 12350, -2323):  # Existing area type 0.
                    new_area = clone_map_area(area)
                    new_area.position.x = 3027
                    new_area.position.y = 12400 - 700
                    new_area.position.z = -16100
                    new_area.scale.x = 14.0  # 700 / 100 * 2 (700 was the radius of the cylinder).
                    new_area.scale.y = 14.0
                    new_area.scale.z = 7.0  # The depth is 700.
                    new_area.rotation = new_area.rotation.default()
                    new_area.rotation.rotate_around_z(0.33)
                    new_areas.append(new_area)

                    new_area = clone_map_area(area)
                    new_area.position.x = 2100
                    new_area.position.y = 16000 - 700
                    new_area.position.z = -10400
                    new_area.scale.x = 14.0  # 700 / 100 * 2 (700 was the radius of the cylinder).
                    new_area.scale.y = 14.0
                    new_area.scale.z = 7.0  # The height was 700.
                    new_area.rotation = new_area.rotation.default()
                    new_area.rotation.rotate_around_z(1.71)
                    new_areas.append(new_area)
            self.level_file.areas.areas.extend(new_areas)

            # Also an area for ceiling (type 2) in the entry pipe, where karts could purposely stand
            # still before fully enterring the pipe (a blue shell could strike).
            new_areas = []
            for area in self.level_file.areas.areas:
                if similar_position(area.position, 7312, 11549, 10576):  # Existing area type 2.
                    new_area = clone_map_area(area)
                    inner_cylinder_factor = 0.75
                    new_area.position.x = 3027
                    new_area.position.y = 12400 - 700 * inner_cylinder_factor
                    new_area.position.z = -16100
                    new_area.scale.x = 14.0 * inner_cylinder_factor
                    new_area.scale.y = 14.0 * inner_cylinder_factor
                    new_area.scale.z = 7.0  # The depth is 700.
                    new_area.rotation = new_area.rotation.default()
                    new_area.rotation.rotate_around_z(0.33)
                    new_areas.append(new_area)
            self.level_file.areas.areas.extend(new_areas)

            # In the pond shortcut, checkpoints need to be tweaked, or else lap completion can
            # break, as there is a sweep gap that karts can go through on the left-hand side.
            for group in self.level_file.checkpoints.groups:
                for point in group.points:
                    if similar_position(point.start, -7386, 31184, 11797):
                        point.start.x = -6158
                        point.start.z = 11076
                        # Also, it seems this flag determines whether the following checkpoints can
                        # be skipped. Swap the values with the original check point that had this
                        # flag set.
                        point.unk1 = 1
                    elif similar_position(point.start, -6067, 31184, 11475):
                        point.unk1 = 0

        elif Course.DKMountain:
            # In DK Mountain, the barrel cannon needs to be replaced, reoriented and reconnected to
            # their correct respawn point.
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, -12640, 7520, 14880):
                    obj.position.x = -357.2
                    obj.position.y = 33150
                    obj.position.z = -56865.157
                    forward, up, left = obj.rotation.get_vectors()
                    forward.x = -0.13015892227286752
                    forward.y = -0.636526839633258
                    forward.z = 0.7601922371211514
                    up.x = -0.10742192358905826
                    up.y = 0.7712545509924055
                    up.z = 0.6273969619833439
                    left.x = 0.9856567279155517
                    left.y = 0.0
                    left.z = 0.16876259868468454
                    obj.rotation.set_vectors(forward, up, left)
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, -375, 34270, -53659):
                    next_enemy_point = 77
                    point.unk1 = next_enemy_point
                    point.position.x = -12391.407
                    point.position.y = 10500
                    point.position.z = 13793.222
                    point.rotation.rotate_around_z(0.2)
            # Enemy points towards the barrel cannon need to be more strict (less scale factor), or
            # else CPU karts can get stuck against the metallic fence.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, 111, 33802, -59231):
                    point.position.x = -3.272
                    point.position.z = -59100.749
                    point.scale = 900
                elif similar_position(point.position, -253, 33824, -57218):
                    point.position.x = -318.927
                    point.position.z = -56857.395
                    point.scale = 700
            # Add an extra respawn point. Karts can now fall through the cliff if the cannon shoots
            # too close to the right-hand side (where the gap is).
            for respawn_point in self.level_file.respawnpoints:
                if respawn_point.respawn_id == 0:
                    new_respawn_point = libbol.JugemPoint.new()
                    new_respawn_point.position.x = -12759.874
                    new_respawn_point.position.y = 8670.48
                    new_respawn_point.position.z = 15182.344
                    new_respawn_point.rotation.set_vectors(*respawn_point.rotation.get_vectors())
                    new_respawn_point.respawn_id = 7
                    next_enemy_point = 76
                    new_respawn_point.unk1 = next_enemy_point
                    new_respawn_point.unk2 = -1
                    new_respawn_point.unk3 = -1
                    self.level_file.respawnpoints.append(new_respawn_point)
            # The path of the camera that was pointing at the billboard and then the cannon will be
            # reversed, so that the billboard is given the light spot.
            for camera in self.level_file.cameras:
                if similar_position(camera.position, -24742, 10233, 14156):
                    camera.position3.x = camera.position2.x
                    camera.position3.y = camera.position2.y
                    camera.position3.z = camera.position2.z
                    camera.position2.x = -21224.457
                    camera.position2.y = 11287.488
                    camera.position2.z = 20326.903
            # And the two static cameras that were pointing at the cannon barrel and landing area
            # will be touched up, so that they show a more relevant view now.
            for camera in self.level_file.cameras:
                if similar_position(camera.position, -15836, 7411, 6958):
                    camera.position.x = -15836.0
                    camera.position.y = 11912.36
                    camera.position.z = 7998.26
                    forward, up, left = camera.rotation.get_vectors()
                    forward.x = 0.3383
                    forward.y = -0.3455
                    forward.z = 0.8753
                    up.x = 0.1412
                    up.y = 0.9383
                    up.z = 0.3158
                    left.x = 0.9304
                    left.y = -0.0168
                    left.z = -0.3662
                    camera.rotation.set_vectors(forward, up, left)
                elif similar_position(camera.position, 1900, 34315, -64800):
                    camera.position.x = 3004.798
                    camera.position.y = 35698.786
                    camera.position.z = -53975.203
                    forward, up, left = camera.rotation.get_vectors()
                    forward.x = -0.5855
                    forward.y = -0.4913
                    forward.z = -0.6448
                    up.x = -0.2891
                    up.y = 0.8696
                    up.z = -0.4002
                    left.x = -0.7574
                    left.y = 0.0479
                    left.z = 0.6512
                    camera.rotation.set_vectors(forward, up, left)
            # And another static camera that was showing the decent needs to be reversed, so that it
            # ends up pointing at the cannon now.
            for camera in self.level_file.cameras:
                if similar_position(camera.position, -16282, 7411, -17102):
                    aux = camera.position2
                    camera.position2 = camera.position3
                    camera.position3 = aux

            # Move item boxes so they can be at reach, and add some more item boxes in the uphill,
            # as it would otherwise be slow paced/boring (compared to the original downhill).
            item_boxes = []
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, 6929, 29455, -58215):
                    item_boxes.append(obj)
                elif similar_position(obj.position, 7309, 29433, -58223):
                    item_boxes.append(obj)
                elif similar_position(obj.position, 7674, 29409, -58220):
                    item_boxes.append(obj)
                elif similar_position(obj.position, 8020, 29434, -58221):
                    item_boxes.append(obj)
            for item_box in item_boxes:
                # Because the slope has been made less steep.
                item_box.position.y = 28840
            for item_box in item_boxes:
                clone_item_box = clone_map_object(item_box)
                clone_item_box.position.x += 700
                clone_item_box.position.y = 23710
                clone_item_box.position.z += 12500
                self.level_file.objects.objects.append(clone_item_box)
            for item_box in item_boxes:
                clone_item_box = clone_map_object(item_box)
                clone_item_box.position.x -= 15300
                clone_item_box.position.y = 14010
                clone_item_box.position.z += 25300
                self.level_file.objects.objects.append(clone_item_box)
            # Move the now last four item boxes closer to the new landing area, or else there is no
            # much time left to use the items in the last lap, as they are too close to the goal.
            for obj in self.level_file.objects.objects:
                a = type(obj.position)(-21302.0, 8429.53, 17943.0)
                b = type(obj.position)(-20593.0, 8370.228, 17565.0)
                if similar_position(obj.position, -16497, 5538, 8549):
                    obj.position = a
                elif similar_position(obj.position, -16113, 5525, 8424):
                    obj.position = a + (b - a) / 3.0
                elif similar_position(obj.position, -15757, 5513, 8308):
                    obj.position = a + (b - a) / 3.0 * 2.0
                elif similar_position(obj.position, -15388, 5495, 8171):
                    obj.position = b
            # Move/Rotate some respawn points that happen to be in an awkward place in this course.
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, -14822, 4078, -2903):
                    next_enemy_point = 4
                    point.unk1 = next_enemy_point
                    point.position.x = -14915.867
                    point.position.y = 5706.045
                    point.position.z = -13338.957
                elif similar_position(point.position, -11801, 7500, -16852):
                    point.position.x = -10801.857
                    point.position.y = 7500.582
                    point.position.z = -16280.864
                    point.rotation.rotate_around_z(pi / 1.5)
                elif similar_position(point.position, -14610, 9166, -28576):
                    point.rotation.rotate_around_z(-pi / 2)
                elif similar_position(point.position, 10505, 20014, -38217):
                    point.rotation.rotate_around_z(pi / 2)
            # Make bridge wider. On start, there are so many karts that some always fall. This is
            # not such a big issue in the original course, as karts scatter during the first lap.
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, -14824, 4826, -8034):
                    obj.scale.x *= 1.15
            # Add some trees to hide the empty space left by the barrel cannon.
            trees = [libbol.MapObject.new() for _ in range(2)]
            for tree in trees:
                tree.presence_filter = 143
                tree.presence = 1  # Hidden in the low-detail version.
            trees[0].objectid = 4505  # TMapObjNoMove_DonkyWood
            trees[0].position.x = -13343.539
            trees[0].position.y = 6655.139
            trees[0].position.z = 12325.512
            trees[0].rotation.rotate_around_z(3.0)
            trees[1].objectid = 4504  # TMapObjDonkyTree
            trees[1].position.x = -13782.259
            trees[1].position.y = 7134.799
            trees[1].position.z = 13170.097
            trees[1].rotation.rotate_around_z(2.7)
            self.level_file.objects.objects.extend(trees)
            # In the original track, the first checkpoint after the cannon shot had the unk2 set. It
            # is unsure at this time what it means, but the logic will be preserved.
            assert checkpointgroups[0].points[56].unk2 == 1
            checkpointgroups[0].points[55].unk2 = 1
            checkpointgroups[0].points[56].unk2 = 0
            # Enemy point at the highest steep slope needs to be tweaked as the slope was also
            # smoothened.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, 7453, 29227, -58297):
                    point.position.y = 29059.793

        elif Course.WarioColosseum:
            # In Wario Colosseum, an invisible cannon needs to be added as a lift.
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, -154, 28824, -61):
                    next_enemy_point = 101
                    point.unk1 = next_enemy_point
                    point.position.x = 1555
                    point.position.y = 32000
                    point.position.z = 667
                    point.rotation = point.rotation.default()
                    point.rotation.rotate_around_z(5.8992)
                    cannon = libbol.MapObject.new()
                    cannon.objectid = 4501  # GeoCannon
                    cannon.position.x = 0
                    cannon.position.y = 30000
                    cannon.position.z = 0
                    cannon.rotation.set_vectors(*point.rotation.get_vectors())
                    cannon.unk_flag = 1  # Collision.
                    cannon.presence_filter = 143
                    cannon.userdata[0] = point.respawn_id
                    cannon.userdata[2] = 1  # Invisible.
                    cannon.userdata[3] = 1  # No idea. In Rainbow Row it is set to 1.
                    self.level_file.objects.objects.append(cannon)
                elif similar_position(point.position, -345, 28758, -141):
                    # Center the respawn point on the boost, which happens to be at the world's
                    # origin.
                    point.position.x = 0
                    point.position.z = 0
            # Some item boxes need to be moved closer to the edge now.
            for obj in self.level_file.objects.objects:
                vertical_offset = 135
                horizontal_offset = 310
                # First four item boxes after starting line.
                if similar_position(obj.position, -5460, 22449, -13210):
                    obj.position.x = -6875 + horizontal_offset
                    obj.position.y = 22179.4 + vertical_offset
                elif similar_position(obj.position, -5460, 22449, -12789):
                    obj.position.x = -6875 + horizontal_offset
                    obj.position.y = 22179.4 + vertical_offset
                elif similar_position(obj.position, -5460, 22449, -12397):
                    obj.position.x = -6875 + horizontal_offset
                    obj.position.y = 22179.4 + vertical_offset
                elif similar_position(obj.position, -5448, 22449, -12006):
                    obj.position.x = -6875 + horizontal_offset
                    obj.position.y = 22179.4 + vertical_offset
                # Last before finish line.
                elif similar_position(obj.position, -861, 23783, 11472):  # Item box and fire balls.
                    obj.position.x = 0.000107 - horizontal_offset
                    obj.position.y = 23793.7 + vertical_offset
                    obj.position.z = 11515.9
                # Last but one before finish line.
                elif similar_position(obj.position, 16030, 25445, 13653):  # Item box.
                    obj.position.x = 16506.1 - horizontal_offset
                    obj.position.y = 25165.8 + vertical_offset
                    obj.position.z = 13705.2
                elif similar_position(obj.position, 16031, 25445, 13653):  # Fire circle.
                    obj.position.x = 16506.1 - horizontal_offset
                    obj.position.y = 25165.8 + vertical_offset
                    obj.position.z = 13705.2
            # Three respawn points need to be moved further away from the jump, so that heavy karts
            # have a chance to speed up before taking the jump.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, 17619, 25365, 13761):
                    respawn_point.position.x = 18446
                elif similar_position(respawn_point.position, 17498, 25365, 13761):
                    respawn_point.position.x = 18446
                elif similar_position(respawn_point.position, 1050, 23793, 11500):
                    respawn_point.position.x = 2540
                elif similar_position(respawn_point.position, -8050, 22179, -12662):
                    respawn_point.position.x = -9516
                elif similar_position(respawn_point.position, -8314, 22179, -12662):
                    respawn_point.position.x = -9516
            # Two respawn points need their next enemy point swapped, as the automatic attempt did
            # not get the values right. These are the two respawn points at the black hole jump.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, 2367, 12793, 1589):
                    respawn_point.unk1 = 35
                elif similar_position(respawn_point.position, -2378, 12793, -1585):
                    respawn_point.unk1 = 33
            # Also fix the preceding checkpoint index of the respawn points.
            self.level_file.respawnpoints[0].unk3 = 5
            self.level_file.respawnpoints[1].unk3 = 70
            self.level_file.respawnpoints[2].unk3 = 67
            self.level_file.respawnpoints[3].unk3 = 59
            self.level_file.respawnpoints[4].unk3 = 23
            self.level_file.respawnpoints[5].unk3 = 15
            self.level_file.respawnpoints[6].unk3 = 15
            self.level_file.respawnpoints[7].unk3 = 62
            self.level_file.respawnpoints[8].unk3 = 33
            self.level_file.respawnpoints[9].unk3 = 7
            self.level_file.respawnpoints[10].unk3 = 47
            self.level_file.respawnpoints[11].unk3 = 43
            self.level_file.respawnpoints[12].unk3 = 15
            self.level_file.respawnpoints[13].unk3 = 16
            self.level_file.respawnpoints[14].unk3 = 67
            self.level_file.respawnpoints[15].unk3 = 59
            self.level_file.respawnpoints[16].unk3 = 35
            self.level_file.respawnpoints[17].unk3 = 70
            self.level_file.respawnpoints[18].unk3 = 5
            # The now first curve is too sharp, and the AI falls too often. They need to be guided
            # to take the jump with the right direction.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, -13182, 22179, -9381):
                    point.position.x = -13600.302
                    point.position.z = -10077.566
                    point.scale = 1000
                elif similar_position(point.position, -12624, 22179, -11330):
                    point.position.x = -12717.216
                    point.position.z = -11887.452
                    point.scale = 1000
                elif similar_position(point.position, -10860, 22179, -12278):
                    point.position.x = -10443.13
                    point.position.z = -12882.196
                    point.scale = 600
                elif similar_position(point.position, -7345, 22179, -12629):
                    point.position.x = -7253.032
                    point.position.z = -12895.782
                    point.scale = 600

        elif Course.DinoDinoJungle:
            # In Dino Dino Jungle, a respawn point needs to be moved after the bridge now. This is
            # the only respawn point in the course with `unk3` (preceding checkpoint index) set, so
            # we will keep it updated.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, 4417, 11016, 2635):
                    next_enemy_point = 13
                    respawn_point.unk1 = next_enemy_point
                    respawn_point.unk3 = 17
                    respawn_point.position.x = -1017.667
                    respawn_point.position.z = -6557.909
            # The automatic attempt to set the next respawn point failed in one respawn point.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, -23680, 12180, -18919):
                    next_enemy_point = 26
                    respawn_point.unk1 = next_enemy_point
            # Cosmetic reorientation of a respawn point.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, -18294, 8952, 12319):
                    respawn_point.rotation.rotate_around_z(0.3)
            # The enemy point routes before the entrance to the bridge need to be shrinked, to guide
            # the AI karts better through the bridge.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, 7127, 11181, 6913):
                    point.position.x = 7352.806
                    point.position.y = 10900.539
                    point.position.z = 7767.463
                    point.scale = 1000
                elif similar_position(point.position, 5661, 11013, 4220):
                    point.position.x = 5030.802
                    point.position.z = 3274.75
                    point.scale = 600
                elif similar_position(point.position, 3114, 11120, 57):
                    point.position.x = 1843.655
                    point.position.z = -2218.857
                    point.scale = 500
                elif similar_position(point.position, -569, 11340, -6093):
                    point.scale = 600
            # Item boxes at the entrace of the bridge need to be moved up the hill.
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, 5177, 11014, 5050):
                    obj.position.x += 640
                    obj.position.y += 175
                    obj.position.z += 1148
                elif similar_position(obj.position, 5666, 11014, 4806):
                    obj.position.x += 640
                    obj.position.y += 175
                    obj.position.z += 1148
                elif similar_position(obj.position, 6150, 11015, 4558):
                    obj.position.x += 640
                    obj.position.y += 175
                    obj.position.z += 1148
                elif similar_position(obj.position, 6623, 11016, 4319):
                    obj.position.x += 640
                    obj.position.y += 175
                    obj.position.z += 1148
            # Enemy points in the long bridge need to be adjusted as well, to guide the AI karts
            # better.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, -28043, 12069, -14909):
                    point.position.x = -27124.985
                    point.position.z = -16269.986
                    point.scale = 1000
                elif similar_position(point.position, -29344, 12069, -13709):
                    point.position.x = -28968.548
                    point.position.z = -14789.323
                    point.scale = 1000
                elif similar_position(point.position, -29532, 12069, -11003):
                    point.position.x = -29679.755
                    point.position.z = -13350.394
                elif similar_position(point.position, -28176, 12069, -9351):
                    point.position.x = -29488.43
                    point.position.z = -11495.028
                    point.scale = 700
                elif similar_position(point.position, -27683, 12069, -7870):
                    point.position.x = -28430.42
                    point.position.z = -9968.252
                    point.scale = 800
                elif similar_position(point.position, -27528, 12069, -5512):
                    point.position.x = -27498.599
                    point.position.z = -8129.775
                    point.scale = 700
                elif similar_position(point.position, -26942, 11992, -3103):
                    point.position.x = -26815.991
                    point.position.y = 11968.697
                    point.position.z = -2817.384
                    point.scale = 400
                elif similar_position(point.position, -25824, 11626, 1291):
                    point.position.x = -25904.194
                    point.position.y = 11642.031
                    point.position.z = 1128.298
                    point.scale = 700
                elif similar_position(point.position, -24980, 11007, 5638):
                    point.position.x = -24936.582
                    point.position.y = 10909.169
                    point.position.z = 6210.55
                    point.scale = 700
                elif similar_position(point.position, -24400, 10341, 8258):
                    point.position.x = -24400.23
                    point.position.y = 10311.652
                    point.position.z = 8258.797
                    point.scale = 800
                elif similar_position(point.position, -23092, 9692, 10347):
                    point.position.x = -22828.33
                    point.position.y = 9624.745
                    point.position.z = 10479.934
                    point.scale = 800
                elif similar_position(point.position, -19378, 9115, 12218):
                    point.position.x = -20170.814
                    point.position.y = 9143.745
                    point.position.z = 12174.146
                    point.scale = 900
                elif similar_position(point.position, -17470, 8866, 12261):
                    point.position.x = -17470.271
                    point.position.y = 8866.754
                    point.position.z = 12261.225
                    point.scale = 700
                elif similar_position(point.position, -15751, 8561, 11559):
                    point.position.x = -15751.235
                    point.position.y = 8561.806
                    point.position.z = 11559.073
                    point.scale = 800
                if similar_position(point.position, -14698, 8251, 9954):
                    point.position.x = -14698.151
                    point.position.y = 8251.187
                    point.position.z = 9954.363
                    point.scale = 900
            # Space out one of the enemy points in the secondary bridge (by the long bridge), to
            # avoid the issue where karts may end up following an items-only enemy point nearby.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, -28089, 11961, -3098):
                    point.position.x = -28452.639
                    point.position.y = 11925.776
                    point.position.z = -2411.521
                    point.scale = 700
            # Last item boxes are not too useful in the last lap. They will be moved a few curves
            # ahead.
            for obj in self.level_file.objects.objects:
                a = type(obj.position)(7149.1, 8427.9, -13575.201)
                b = type(obj.position)(8414.3, 8427.9, -14464.9)
                if similar_position(obj.position, 10323, 8427, -18460):
                    obj.position = a
                elif similar_position(obj.position, 10523, 8427, -18908):
                    obj.position = a + (b - a) / 3.0
                elif similar_position(obj.position, 10727, 8427, -19352):
                    obj.position = a + (b - a) / 3.0 * 2.0
                elif similar_position(obj.position, 10943, 8427, -19846):
                    obj.position = b

            # With the platform being raised (for enabling the alternate path), enemy points and
            # item boxes need to be tweaked.
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, -15375, 11163, -12717):
                    obj.position.y += 2000
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, -9591, 11944, -12840):
                    point.position.y = 12283.523
                elif similar_position(point.position, -12826, 11345, -12765):
                    point.position.x = -14124.813
                    point.position.y = 12975.959
                elif similar_position(point.position, -16940, 11163, -12643):
                    point.position.y += 2000
                elif similar_position(point.position, -21012, 12368, -13661):
                    point.position.x = -20763.656
                    point.position.y = 13379.541
                    point.position.z = -13383.43

        elif Course.BowsersCastle:
            # In Bowser's Castle, the last respawn point needs to be tweaked to prevent a crash when
            # karts touch the associated dead zone (`0x0F00`). If we don't move it, then its
            # preceding checkpoint would be the last checkpoint, which causes a crash in the game.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, 3600, 8109, 13150):
                    respawn_point.position.x = 3600.329
                    respawn_point.position.y = 7175.91
                    respawn_point.position.z = 6116.826
                    respawn_point.unk3 = 62  # Preceding checkpoint.
            # The respawn points near the old final jump (where the new wooden bridge is now) can
            # be advanced a little bit, so the penalty is a bit less stressed.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, -2266, 8518, 24767):
                    respawn_point.position.x = -6265.218
                    respawn_point.position.y = 10193.2
                    respawn_point.unk1 = 7  # Next enemy point.
                    respawn_point.unk3 = 5  # Preceding checkpoint.
                elif similar_position(respawn_point.position, -2755, 8662, 24777):
                    respawn_point.position.x = -6265.218
                    respawn_point.position.y = 10193.2
                    respawn_point.unk1 = 7  # Next enemy point.
                    respawn_point.unk3 = 5  # Preceding checkpoint.
            # A respawn point (near the lava shortcut) is too close to the edge.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, -25361, 8819, 20850):
                    respawn_point.position.x = -26502.2
                    respawn_point.position.z = 20968.8
                    respawn_point.rotation.rotate_around_z(0.8)
                    respawn_point.unk1 = 33  # Next enemy point.
            # Another respawn point too close to a cliff.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, -11688, 5856, -12973):
                    respawn_point.position.x = -11723.361
                    respawn_point.position.z = -10801.091
                    respawn_point.unk1 = 87
            # A respawn point that needs to be rotated, as it's facing a wall.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, -3153, 9010, 15136):
                    respawn_point.position.x = -3093.5
                    respawn_point.position.z = 15636.799
                    respawn_point.rotation.rotate_around_z(-pi / 2)
            # A couple of respawn points need to be rotated slightly, as they are rather facing to
            # the lava again.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, -30462, 8116, 17398):
                    respawn_point.position.x = -31302.455
                    respawn_point.position.z = 17083.891
                    respawn_point.rotation.rotate_around_z(-0.8)
                elif similar_position(respawn_point.position, -30371, 8132, 17941):
                    respawn_point.position.x = -31248.616
                    respawn_point.position.z = 17777.162
                    respawn_point.rotation.rotate_around_z(-0.8)
            # Some enemy points need to be slightly replaced, or else the AI karts can be too dumb
            # against walls.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, -11704, 6378, -3558):
                    point.scale = 1000
                elif similar_position(point.position, -11690, 6350, -6038):
                    point.scale = 800
                elif similar_position(point.position, -11711, 6213, -9293):
                    point.scale = 700
                elif similar_position(point.position, 2265, 6937, -17314):
                    point.position.x = 2485.527
                    point.position.z = -19180.256
                    point.scale = 700
                elif similar_position(point.position, 2229, 6937, -25547):
                    point.position.x = 1947.2
                    point.position.z = -26168.349
                elif similar_position(point.position, 3168, 6937, -24698):
                    point.position.x = 3186.967
                    point.position.z = -25770.094
                elif similar_position(point.position, 3530, 6937, -23212):
                    point.position.x = 3662.113
                    point.position.z = -25035.881
                elif similar_position(point.position, 3641, 6937, -21705):
                    point.position.x = 3644.253
                    point.position.z = -23567.157
                    point.scale = 800
                elif similar_position(point.position, 4931, 6937, -17307):
                    point.position.x = 4639.296
                    point.position.z = -19156.552
                    point.scale = 700
                elif similar_position(point.position, 2408, 6937, -9105):
                    point.position.x = 2290.373
                    point.position.z = -10052.781
                    point.scale = 700
                elif similar_position(point.position, 4735, 6937, -9131):
                    point.position.x = 4883.738
                    point.position.z = -10048.809
                    point.scale = 700
                elif similar_position(point.position, 3583, 6757, -4287):
                    point.position.z = -963.815
                    point.scale = 700
                elif similar_position(point.position, 3613, 6757, -347):
                    point.position.z = 989.591
                    point.scale = 700
                elif similar_position(point.position, 3587, 6757, 1770):
                    point.position.z = 2983.638
                    point.scale = 500
                elif similar_position(point.position, -24785, 8829, 21205):
                    point.position.x = -25600.074
                    point.position.z = 21831.697
                elif similar_position(point.position, -21764, 8829, 21243):
                    point.position.x = -22101.443
                    point.position.z = 22001.798
                    point.scale = 1000
                elif similar_position(point.position, -19036, 8829, 21244):
                    point.position.x = -19105.667
                    point.position.z = 21906.953
                elif similar_position(point.position, -24457, 8829, 22795):
                    point.position.x = -25248.8
                    point.position.z = 22141.699
            # Enemy point at the stretched segment is adjusted.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, -11690, 6350, -6038):
                    point.position.x = -11690.782
                    point.position.y = 6817.032
                    point.position.z = -7371.771
            # The old area (type 5) that was present in the last jump needs to be removed as there
            # is no jump anymore. (At this point, it is not fully known what these area types mean,
            # but they always appear in jumps.)
            for area in list(self.level_file.areas.areas):
                if similar_position(area.position, -7263, 6057, 25103):
                    self.level_file.areas.areas.remove(area)
                    break

        elif Course.RainbowRoad:
            # In Rainbow Road, the cannon needs to be replaced, and its orientation flipped.
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, 13547, 7964, 14490):
                    obj.position.x = 7621.652
                    obj.position.y = 65516.91
                    obj.position.z = 6343.7
                    obj.rotation.rotate_around_z(pi)
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, 7621, 65516, 6343):
                    next_enemy_point = 26
                    point.unk1 = next_enemy_point
                    point.position.x = 13906.3
                    point.position.y = 8500
                    point.position.z = 14914.621
            # The long segment that has been rotated needs their enemy points tweaked, and its
            # respawn point. And some item boxes can be added as well.
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, -8990, 22984, 3537):
                    next_enemy_point = 70
                    point.unk1 = next_enemy_point
                    point.position.x = -9249.727
                    point.position.y = 22461.048
                    point.position.z = 3967.685
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, -14867, 20691, 10641):
                    point.position.y = 19381.551
                elif similar_position(point.position, -11961, 21620, 7157):
                    point.position.y = 19849.914
                elif similar_position(point.position, -9249, 22818, 3967):
                    point.position.y = 22392.346
                elif similar_position(point.position, -6875, 24294, 1120):
                    point.position.y = 25216.322
                elif similar_position(point.position, -4564, 26504, -1539):
                    point.position.y = 28761.83
                elif similar_position(point.position, -2634, 29975, -3932):
                    point.position.y = 32465.757
            item_boxes = (libbol.MapObject.new(), libbol.MapObject.new())
            for item_box in item_boxes:
                item_box.objectid = 1  # GeoItemBox
                item_box.position.x = -9261.935
                item_box.position.y = 22791.51
                item_box.position.z = 2932.105
                item_box.unk_flag = 1  # Collision.
                item_box.presence_filter = 15
                item_box.presence = 3
                item_box.userdata[0] = 135  # Height offset.
                item_box.userdata[1] = 0  # Item box type.
                self.level_file.objects.objects.append(item_box)
            item_boxes[1].position.x = -8246.143
            item_boxes[1].position.z = 3801.24
            # In the last touched segment, the respawn point and enemy points need to be lifted as
            # well.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, -5343, 50436, -27863):
                    respawn_point.position.x = -4292.75
                    respawn_point.position.y = 50561.184
                    respawn_point.position.z = -27066.865
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, -4139, 49580, -26973):
                    point.position.y = 50415.15
                elif similar_position(point.position, -7473, 52432, -29655):
                    point.position.y = 54395.957
                elif similar_position(point.position, -12407, 58319, -33607):
                    point.position.y = 60546.483
            # Some curves are too sharp for the AI in reverse; they need to be smoothened.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, 19875, 4392, 24030):
                    point.position.x = 20411.309
                    point.position.z = 23816.118
                    point.scale = 1600
                elif similar_position(point.position, 20176, 4409, 26006):
                    point.position.x = 20444.041
                    point.position.z = 26166.851
                    point.scale = 1200
                elif similar_position(point.position, 18582, 4532, 27035):
                    point.position.x = 18957.739
                    point.position.z = 27035.482
                    point.scale = 1200
                elif similar_position(point.position, 16228, 4806, 27090):
                    point.position.x = 16228.193
                    point.position.z = 27090.387
                    point.scale = 1000
                elif similar_position(point.position, 14143, 5130, 27341):
                    point.position.x = 13981.014
                    point.position.z = 27509.902
                    point.scale = 600
                elif similar_position(point.position, 12035, 5578, 28432):
                    point.position.x = 11688.665
                    point.position.z = 28664.941
                    point.scale = 600
                elif similar_position(point.position, 9888, 5978, 28549):
                    point.position.x = 9728.025
                    point.position.z = 28602.795
                    point.scale = 700
                elif similar_position(point.position, 7648, 6349, 27478):
                    point.position.x = 7469.984
                    point.position.z = 27620.968
                    point.scale = 1000
                elif similar_position(point.position, 5469, 7125, 27435):
                    point.position.x = 5369.341
                    point.position.z = 27664.288
                    point.scale = 1000
                elif similar_position(point.position, 3287, 8390, 28683):
                    point.position.x = 3081.368
                    point.position.z = 28699.229
                    point.scale = 700
                elif similar_position(point.position, 974, 9862, 28837):
                    point.position.x = 759.938
                    point.position.z = 28784.281
                    point.scale = 1000
                elif similar_position(point.position, -1650, 11405, 27634):
                    point.position.x = -2025.317
                    point.position.z = 27634.963
                    point.scale = 1100
                elif similar_position(point.position, -4498, 13196, 27019):
                    point.position.x = -4391.181
                    point.position.z = 27072.629
                    point.scale = 1500
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, 11856, 5668, 28795):
                    respawn_point.position.x = 12975.166
                    respawn_point.position.z = 28050.46
                    respawn_point.unk1 = 33
            # AI karts need to be guided away from the fences in the uphill, or else they could get
            # stuck.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, 2367, 34102, -9713):
                    point.position.x = 2689.621
                    point.position.z = -9825.396
                elif similar_position(point.position, 2555, 34864, -11693):
                    point.position.x = 2905.119
                    point.position.z = -11903.349
                elif similar_position(point.position, 1752, 34893, -12407):
                    point.position.x = 1668.699
                    point.position.z = -12827.196
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, -707, 41904, -15320):
                    point.position.x = -474.109
                    point.position.z = -15378.421
                elif similar_position(point.position, 3, 43740, -18295):
                    point.position.x = 178.815
                    point.position.z = -18295.631
                elif similar_position(point.position, -158, 45391, -21875):
                    point.position.x = 191.668
                    point.position.z = -21934.154
                elif similar_position(point.position, -1306, 47478, -24337):
                    point.position.x = -1073.024
                    point.position.z = -24395.509
            # Rather cosmetic changes to avoid being spawned against a wall or cliff.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, 20460, 4392, 24193):
                    respawn_point.rotation.rotate_around_z(-0.7)
                elif similar_position(respawn_point.position, 2584, 34419, -10326):
                    respawn_point.rotation.rotate_around_z(0.5)
            # Add an extra respawn point for the last jump's boost ramp.
            for respawn_point in self.level_file.respawnpoints:
                if respawn_point.respawn_id == 1:
                    new_respawn_point = libbol.JugemPoint.new()
                    new_respawn_point.position.x = -12805.031
                    new_respawn_point.position.y = 58322.961
                    new_respawn_point.position.z = -33971.535
                    new_respawn_point.rotation.set_vectors(*respawn_point.rotation.get_vectors())
                    new_respawn_point.respawn_id = 14
                    new_respawn_point.unk1 = 92
                    new_respawn_point.unk2 = -1
                    new_respawn_point.unk3 = -1
                    self.level_file.respawnpoints.append(new_respawn_point)
            # Also fix the preceding checkpoint index of the respawn points.
            self.level_file.respawnpoints[0].unk3 = 16
            self.level_file.respawnpoints[1].unk3 = 59
            self.level_file.respawnpoints[2].unk3 = 50
            self.level_file.respawnpoints[3].unk3 = 43
            self.level_file.respawnpoints[4].unk3 = 39
            self.level_file.respawnpoints[5].unk3 = 36
            self.level_file.respawnpoints[6].unk3 = 33
            self.level_file.respawnpoints[7].unk3 = 29
            self.level_file.respawnpoints[8].unk3 = 25
            self.level_file.respawnpoints[9].unk3 = 23
            self.level_file.respawnpoints[10].unk3 = 20
            self.level_file.respawnpoints[11].unk3 = 18
            self.level_file.respawnpoints[12].unk3 = 13
            self.level_file.respawnpoints[13].unk3 = 10
            self.level_file.respawnpoints[14].unk3 = 61


def find_file(rarc_folder, ending):
    for filename in rarc_folder.files.keys():
        if filename.endswith(ending):
            return filename
    raise RuntimeError("No Course File found!")


def get_file_safe(rarc_folder, ending):
    for filename in rarc_folder.files.keys():
        if filename.endswith(ending):
            return rarc_folder.files[filename]
    return None


import sys
def except_hook(cls, exception, traceback):
    sys.__excepthook__(cls, exception, traceback)



POTENTIALLY_EDITING_EVENTS = (
    QtCore.QEvent.KeyRelease,
    QtCore.QEvent.MouseButtonRelease,
)


class Application(QtWidgets.QApplication):

    document_potentially_changed = QtCore.Signal()

    def notify(self, receiver: QtCore.QObject, event: QtCore.QEvent) -> bool:
        if event.type() in POTENTIALLY_EDITING_EVENTS:
            if isinstance(receiver, QtGui.QWindow):
                QtCore.QTimer.singleShot(0, self.document_potentially_changed)

        return super().notify(receiver, event)


if __name__ == "__main__":
    #import sys
    import platform
    import signal
    import argparse

    QtCore.QLocale.setDefault(QtCore.QLocale(QtCore.QLocale.English))

    sys.excepthook = except_hook

    parser = argparse.ArgumentParser()
    parser.add_argument("--load", default=None,
                        help="Path to the ARC or BOL file to be loaded.")
    parser.add_argument("--additional", default=None, choices=['model', 'collision'],
                        help="Whether to also load the additional BMD file (3D model) or BCO file "
                        "(collision file).")
    parser.add_argument("--reverse", action='store_true',
                        help="If specified, the loaded file will be reversed. The program will "
                        "exit after that.")

    args = parser.parse_args()

    os.environ['QT_ENABLE_HIGHDPI_SCALING'] = '0'
    app = Application(sys.argv)

    signal.signal(signal.SIGINT, lambda _signal, _frame: app.quit())

    app.setStyle(QtWidgets.QStyleFactory.create("Fusion"))

    role_colors = []
    role_colors.append((QtGui.QPalette.Window, QtGui.QColor(60, 60, 60)))
    role_colors.append((QtGui.QPalette.WindowText, QtGui.QColor(200, 200, 200)))
    role_colors.append((QtGui.QPalette.Base, QtGui.QColor(25, 25, 25)))
    role_colors.append((QtGui.QPalette.AlternateBase, QtGui.QColor(60, 60, 60)))
    role_colors.append((QtGui.QPalette.ToolTipBase, QtGui.QColor(40, 40, 40)))
    role_colors.append((QtGui.QPalette.ToolTipText, QtGui.QColor(200, 200, 200)))
    try:
        role_colors.append((QtGui.QPalette.PlaceholderText, QtGui.QColor(160, 160, 160)))
    except AttributeError:
        pass
    role_colors.append((QtGui.QPalette.Text, QtGui.QColor(200, 200, 200)))
    role_colors.append((QtGui.QPalette.Button, QtGui.QColor(55, 55, 55)))
    role_colors.append((QtGui.QPalette.ButtonText, QtGui.QColor(200, 200, 200)))
    role_colors.append((QtGui.QPalette.BrightText, QtCore.Qt.red))
    role_colors.append((QtGui.QPalette.Light, QtGui.QColor(65, 65, 65)))
    role_colors.append((QtGui.QPalette.Midlight, QtGui.QColor(60, 60, 60)))
    role_colors.append((QtGui.QPalette.Dark, QtGui.QColor(45, 45, 45)))
    role_colors.append((QtGui.QPalette.Mid, QtGui.QColor(50, 50, 50)))
    role_colors.append((QtGui.QPalette.Shadow, QtCore.Qt.black))
    role_colors.append((QtGui.QPalette.Highlight, QtGui.QColor(45, 140, 225)))
    role_colors.append((QtGui.QPalette.HighlightedText, QtCore.Qt.black))
    role_colors.append((QtGui.QPalette.Link, QtGui.QColor(40, 130, 220)))
    role_colors.append((QtGui.QPalette.LinkVisited, QtGui.QColor(110, 70, 150)))
    palette = QtGui.QPalette()
    for role, color in role_colors:
        palette.setColor(QtGui.QPalette.Disabled, role, QtGui.QColor(color).darker())
        palette.setColor(QtGui.QPalette.Active, role, color)
        palette.setColor(QtGui.QPalette.Inactive, role, color)
    app.setPalette(palette)

    QtWidgets.QToolTip.setPalette(palette)
    padding = app.fontMetrics().height() // 2
    app.setStyleSheet(f'QToolTip {{ padding: {padding}px; }}')

    if platform.system() == "Windows":
        import ctypes
        myappid = 'P2GeneratorsEditor'  # arbitrary string
        ctypes.windll.shell32.SetCurrentProcessExplicitAppUserModelID(myappid)

    os.makedirs("lib/temp", exist_ok=True)

    with open("log.txt", "w") as f:
        #sys.stdout = f
        #sys.stderr = f
        print("Python version: ", sys.version)
        editor_gui = GenEditor()
        editor_gui.setWindowIcon(QtGui.QIcon('resources/icon.ico'))

        app.document_potentially_changed.connect(
            editor_gui.on_document_potentially_changed)

        editor_gui.show()

        if args.load is not None:
            if args.reverse:
                def reverse_save_exit():
                    editor_gui.load_file(args.load)
                    try:
                        editor_gui.action_reverse_official_track()
                        editor_gui.button_save_level()
                    except:
                        traceback.print_exc()
                        os._exit(1)
                    os._exit(0)

                editor_gui.hide()
                QtCore.QTimer.singleShot(0, reverse_save_exit)
            else:
                def load():
                    editor_gui.load_file(args.load, additional=args.additional)

                QtCore.QTimer.singleShot(0, load)

        err_code = app.exec()

    sys.exit(err_code)