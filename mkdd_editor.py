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

        def rotate_selection():
            default = rotate_selection.last_value if hasattr(rotate_selection, 'last_value') else 0
            value, ok = QtWidgets.QInputDialog.getDouble(self,
                                                         'Rotate Selection',
                                                         'Z Angle (radians):',
                                                         default,
                                                         decimals=4)
            if not value or not ok:
                return
            rotate_selection.last_value = value
            for rotation in self.level_view.selected_rotations:
                rotation.rotate_around_z(value)

        rotate_selection_action = self.misc_menu.addAction("Rotate Selection")
        rotate_selection_action.setShortcut("Ctrl+Shift+R")
        rotate_selection_action.triggered.connect(rotate_selection)

        def clipboard_changed(mode):
            if mode != 0:
                return

            text = QtWidgets.QApplication.clipboard().text()

            self.level_view.last_clipboard_positions = []

            text = text.replace(',', ' ')
            text = text.replace('.position', ' ')
            text = text.replace('.x', ' ')
            text = text.replace('.y', ' ')
            text = text.replace('.z', ' ')
            text = text.replace('similar_position', ' ')
            text = text.replace('respawn_point', ' ')
            text = text.replace('point', ' ')
            text = text.replace('area', ' ')
            text = text.replace('elif', ' ')
            text = text.replace('if', ' ')
            text = text.replace(':', ' ')
            text = text.replace('(', ' ')
            text = text.replace(')', ' ')
            text = text.replace('=', ' ')

            words = tuple(w.strip() for w in text.split() if w)

            if len(words) % 3 == 0:
                for i in range(0, len(words), 3):
                    try:
                        x = float(words[i])
                        y = float(words[i + 1])
                        z = float(words[i + 2])
                        self.level_view.last_clipboard_positions.append((x, y, z))
                    except ValueError:
                        pass

            self.update_3d()

        QtWidgets.QApplication.clipboard().changed.connect(clipboard_changed)

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

                modelIndex = self.indexAt(event.position().toPoint())
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

        def move_swerve(x, y, z, x2, y2, z2):
            for src in self.level_file.enemypointgroups.points():
                if not similar_position(src.position, x, y, z):
                    continue
                for dst in self.level_file.enemypointgroups.points():
                    if not similar_position(dst.position, x2, y2, z2):
                        continue
                    dst.swerve = src.swerve
                    src.swerve = 0
                    return
            raise AssertionError('Swerve in enemy points not moved')

        def swap_swerve(x, y, z, x2, y2, z2):
            for a in self.level_file.enemypointgroups.points():
                if not similar_position(a.position, x, y, z):
                    continue
                for b in self.level_file.enemypointgroups.points():
                    if not similar_position(b.position, x2, y2, z2):
                        continue
                    a.swerve, b.swerve = b.swerve, a.swerve
                    return
            raise AssertionError('Swerve in enemy points not swapped')

        def set_swerve(x, y, z, swerve):
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, x, y, z):
                    point.swerve = swerve
                    return
            raise AssertionError('Swerve in enemy point not set')

        def move_drift(x, y, z, x2, y2, z2):
            for src in self.level_file.enemypointgroups.points():
                if not similar_position(src.position, x, y, z):
                    continue
                for dst in self.level_file.enemypointgroups.points():
                    if not similar_position(dst.position, x2, y2, z2):
                        continue
                    dst.driftdirection = src.driftdirection
                    dst.driftacuteness = src.driftacuteness
                    dst.driftduration = src.driftduration
                    src.driftdirection = 0
                    src.driftacuteness = 0
                    src.driftduration = 0
                    return
            raise AssertionError('Drifting in enemy points not moved')

        def swap_drift(x, y, z, x2, y2, z2):
            for a in self.level_file.enemypointgroups.points():
                if not similar_position(a.position, x, y, z):
                    continue
                for b in self.level_file.enemypointgroups.points():
                    if not similar_position(b.position, x2, y2, z2):
                        continue
                    a.driftdirection, b.driftdirection = b.driftdirection, a.driftdirection
                    a.driftacuteness, b.driftacuteness = b.driftacuteness, a.driftacuteness
                    a.driftduration, b.driftduration = b.driftduration, a.driftduration
                    return
            raise AssertionError('Drifting in enemy points not swapped')

        def set_drift(x, y, z, direction, acuteness, duration):
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, x, y, z):
                    point.driftdirection = direction
                    point.driftacuteness = acuteness
                    point.driftduration = duration
                    return
            raise AssertionError('Drifting in enemy point not set')

        def del_enemy_point(x, y, z):
            for i, point in enumerate(list(self.level_file.enemypointgroups.points())):
                if similar_position(point.position, x, y, z):
                    for group in self.level_file.enemypointgroups.groups:
                        if point in group.points:
                            group.points.remove(point)
                            for respawn_point in self.level_file.respawnpoints:
                                if respawn_point.unk1 > i:
                                    respawn_point.unk1 -= 1
                            return
            raise AssertionError('Enemy point not deleted')

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
            new_area.shape = area.shape
            new_area.area_type = area.area_type
            new_area.camera_index = area.camera_index
            new_area.feather.i0 = area.feather.i0
            new_area.feather.i1 = area.feather.i1
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
            itemsonly = group.points[0].itemsonly
            group.points[0].itemsonly = 0

            for point in group.points:
                # Enemy points with drifting enabled will only reverse their drifting direction.
                if point.driftdirection:
                    point.driftdirection = 1 if point.driftdirection == 2 else 2

                # Swerve needs to be reversed as well.
                point.swerve *= -1

            group.points.reverse()

            group.points[0].itemsonly = itemsonly

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
        all_segments = collections.OrderedDict()  # Ordered set.
        for group in self.level_file.enemypointgroups.groups:
            # Convert to string. It will be replaced with the new integer value.
            group.points[0].link = str(group.points[0].link)
            group.points[-1].link = str(group.points[-1].link)
            segment = (group.points[0].link, group.points[-1].link)
            if first_segment is None:
                first_segment = segment
            all_segments[segment] = None
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
        self.level_file.enemypointgroups.groups.sort(key=lambda group: group.points[0].itemsonly)
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

        if Course.LuigiCircuit or Course.LuigiCircuit2:
            if Course.LuigiCircuit2:
                # Enemy points at the entrance of the boost pad need to be reduced, so that karts
                # don't take a wrong turn in the last second (they wouldn't struggle to get in track
                # since there are concrete walls). This only affects the fast Luigi Circuit ("2"),
                # as in the 50cc version there are walls that stop karts from taking wrong turns.
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

                # Similarly, some checkpoints need to be tweaked, or else the lap completion
                # progress is restarted if karts take the wrong turn by accident. Things can still
                # go wrong if the player proceeds to drive in the wrong direction for a long time,
                # but at least accidents are prevented.
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

            move_drift(3730, 3291, 21276, 9202, 3537, 23354)
            set_drift(-12118, 56, -27173, 2, 150, 150)

            if Course.LuigiCircuit:
                move_swerve(-9178, 96, -30958, -836, 31, -25916)
            else:
                move_swerve(-9178, 96, -30958, -1376, 70, -28406)

            for obj in self.level_file.objects.objects:
                # Turn sunflowers.
                if obj.objectid == 3703:  # GeoMarioFlower1
                    obj.rotation.rotate_around_z(-1.9)

                # Move some of the flowers that otherwise line up poorly.
                if Course.LuigiCircuit2:
                    if similar_position(obj.position, 8322, 3251, 7337):
                        obj.position.x = 8912.0
                        obj.position.z = 7053.8
                    elif similar_position(obj.position, 2084, 2066, -744):
                        obj.position.x = 3051.6
                        obj.position.z = -1145.2

                # Some trees need to be rotated slightly.
                if similar_position(obj.position, -20019, 922, -27784):
                    obj.rotation.rotate_around_z(-0.4)
                if similar_position(obj.position, -19065, 996, -25158):
                    obj.rotation.rotate_around_z(-0.8)
                if similar_position(obj.position, -1274, 3186, 8996):
                    obj.rotation.rotate_around_z(-0.8)
                if similar_position(obj.position, 472, 3277, 10672):
                    obj.rotation.rotate_around_z(-1.4)

        elif Course.PeachBeach:
            # In Peach Beach, the respan points around the pipe shortcut didn't need to be rotated
            # 180 degrees. They need to be rotated back.
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, 13394, 4863, 26497):
                    point.rotation.rotate_around_z(pi)

                    # Also, since the original pipe's entry is now the exit, the associated respawn
                    # point needs to be put at the teleport's new exit.
                    point.position.x = 13500
                    point.position.y = 2160
                    point.position.z = 26578
                    point.unk3 = 17  # Previous checkpoint.

                elif similar_position(point.position, 13404, 1985, 26490):
                    point.rotation.rotate_around_z(pi)
            # And a few others that need to be slightly tweaked.
            for point in self.level_file.respawnpoints:
                if similar_position(point.position, 3530, 810, -25778):
                    point.position.x = 4958.111
                    point.position.z = -25683.032
                elif similar_position(point.position, -4813, 810, -16010):
                    point.rotation.rotate_around_z(-0.5)
                elif similar_position(point.position, 3348, 810, -3777):
                    point.rotation.rotate_around_z(-0.2)
                elif similar_position(point.position, 665, 810, 14065):
                    point.rotation.rotate_around_z(-0.3)
                elif similar_position(point.position, -8297, 968, 20237):
                    point.rotation.rotate_around_z(1.3)
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

            # And the lone tree needs to be rotated.
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, -13119, 914, 3374):
                    obj.rotation.rotate_around_z(3.2)

            for point in self.level_file.enemypointgroups.points():
                # An enemy point near Cock Rock needs to be tweak, or else karts deviate too much to
                # the shore.
                if similar_position(point.position, -9600, 678, -7950):
                    point.position.x = -8819.2
                    point.position.z = -8429.6
                # An two more in the last curve before the goal (near the pipe shortcut).
                elif similar_position(point.position, 7925, 2179, 24059):
                    point.position.x = 7873.371
                    point.position.z = 23745.284
                elif similar_position(point.position, 9168, 2583, 21531):
                    point.position.x = 9011.303
                    point.position.z = 21269.924

            for obj in list(self.level_file.objects.objects):
                # Item box in the now pipe exit can be removed. The player needs to target the items
                # in the road instead.
                if similar_position(obj.position, 12662, 5361, 26497):
                    self.level_file.objects.objects.remove(obj)

            # Add areas for ceiling and shadow at the entrace of the new pipe.
            new_areas = []
            for area in self.level_file.areas.areas:
                if similar_position(area.position, 13566, 1839, 26568):  # Existing area type 0.
                    # The original shadow area needs to be tweaked a little, to cover the karts that
                    # may have been hit by a blue shell, as the pipe is more more transitable.
                    area.position.y = 2122.313
                    area.scale.y = 12

                    # Shadow area in the new pipe.
                    new_area = clone_map_area(area)
                    new_area.position.x = -9705.0
                    new_area.position.y = 591.516
                    new_area.position.z = 23085
                    new_area.scale.x = 11
                    new_area.scale.y = 8
                    new_area.scale.z = 15
                    new_area.rotation = new_area.rotation.default()
                    new_area.rotation.rotate_around_z(pi / 2)
                    new_areas.append(new_area)

                    # Area type 2 (ceiling).
                    new_area = clone_map_area(new_area)
                    new_area.area_type = 2
                    new_area.position.z = 22898.171  # To cover the border a bit better.
                    new_areas.append(new_area)
            self.level_file.areas.areas.extend(new_areas)

            move_drift(-431, 714, -22500, 8956, 1174, -22387)
            set_drift(-9000, 776, -15100, 1, 60, 150)
            set_drift(-3736, 1245, 20035, 1, 160, 170)

            set_swerve(-3067, 1463, 22469, -1)
            set_swerve(-789, 1786, 25251, -1)

        elif Course.BabyPark:
            move_drift(8730, 6000, -2281, 9100, 6000, 2290)
            move_drift(-8871, 6000, 1921, -9116, 6000, -2117)

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
                a = type(obj.position)(-20782, 5689, -29392)
                b = type(obj.position)(-19979, 5367, -27748)
                if similar_position(obj.position, -26163, 5440, -12651):
                    obj.position = a
                elif similar_position(obj.position, -25657, 5442, -12651):
                    obj.position = a + (b - a) / 3.0
                elif similar_position(obj.position, -25151, 5444, -12651):
                    obj.position = a + (b - a) / 3.0 * 2.0
                elif similar_position(obj.position, -24658, 5445, -12651):
                    obj.position = b

                elif similar_position(obj.position, -15221, 5348, -28576):
                    obj.position = type(obj.position)(-10949, 4753, -25752)
                elif similar_position(obj.position, -14817, 5590, -29861):
                    obj.position = type(obj.position)(-10545, 4722, -27037)
                elif similar_position(obj.position, -14293, 5205, -27932):
                    obj.position = type(obj.position)(-10022, 4649, -25109)
                elif similar_position(obj.position, -14909, 5092, -27365):
                    obj.position = type(obj.position)(-10638, 4743, -24541)
                elif similar_position(obj.position, -14136, 5414, -29153):
                    obj.position = type(obj.position)(-9865, 4592, -26329)

                # Reorient dancing cactus.
                if obj.objectid == 5001:  # TMapObjSanbo
                    obj.rotation.rotate_around_z(pi)

                # Some need some custom tweaks.
                if similar_position(obj.position, -7067, 4396, -24856):
                    obj.rotation.rotate_around_z(0.3)
                elif similar_position(obj.position, -1953, 4248, -24225):
                    obj.rotation.rotate_around_z(-0.05)
                    obj.position.x = -1090.1
                    obj.position.z = -24756.2
                elif similar_position(obj.position, 4369, 4478, -24133):
                    obj.rotation.rotate_around_z(0.4)
                elif similar_position(obj.position, 13709, 5882, 14097):
                    obj.rotation.rotate_around_z(-0.3)
                # Item box between the two cactus is moved too.
                elif similar_position(obj.position, 13895, 5898, 14539):
                    obj.position.x = 14036.391
                    obj.position.z = 14493.3
                elif similar_position(obj.position, 14084, 5915, 15000):
                    obj.rotation.rotate_around_z(-0.3)
                    obj.position.x = 14424.585
                    obj.position.z = 14747.787

                # Trees need to be rotated too.
                elif similar_position(obj.position, 20987, 5396, 10178):
                    obj.rotation.rotate_around_z(1.3)
                elif similar_position(obj.position, 25702, 5000, 8467):
                    obj.rotation.rotate_around_z(1.3)
                elif similar_position(obj.position, 31970, 5696, 7000):
                    obj.rotation.rotate_around_z(1.3)
                elif similar_position(obj.position, 28729, 5283, 2527):
                    obj.rotation.rotate_around_z(1.0)
                elif similar_position(obj.position, 36000, 6502, -2836):
                    obj.rotation.rotate_around_z(1.0)
                elif similar_position(obj.position, 27193, 4888, -6406):
                    obj.rotation.rotate_around_z(1.0)
                elif similar_position(obj.position, 31397, 5555, -7192):
                    obj.rotation.rotate_around_z(1.0)
                elif similar_position(obj.position, 39103, 7395, -10092):
                    obj.rotation.rotate_around_z(0.3)
                elif similar_position(obj.position, 31454, 5863, -12869):
                    obj.rotation.rotate_around_z(1.1)
                elif similar_position(obj.position, 28554, 5738, -19415):
                    obj.rotation.rotate_around_z(1.5)
                elif similar_position(obj.position, 24307, 5946, -24003):
                    obj.rotation.rotate_around_z(1.1)
                elif similar_position(obj.position, 23186, 6119, -27499):
                    obj.rotation.rotate_around_z(0.8)

                elif similar_position(obj.position, 6462, 5122, 3815):
                    obj.rotation.rotate_around_z(-1.9)
                elif similar_position(obj.position, 10763, 5122, 2525):
                    obj.rotation.rotate_around_z(-1.3)
                elif similar_position(obj.position, 7550, 5122, -4077):
                    obj.rotation.rotate_around_z(-1.1)
                elif similar_position(obj.position, 9424, 5122, -9323):
                    obj.rotation.rotate_around_z(-1.0)
                elif similar_position(obj.position, 14074, 5312, -19139):
                    obj.rotation.rotate_around_z(-2.0)

            # The object path of the sand pillar can be reversed (or generally tweaked) as well.
            for route in self.level_file.routes:
                if similar_position(route.points[0].position, 16132, 5246, 4455):
                    route.points.reverse()
                    for _ in range(16):
                        route.points.append(route.points.pop(0))

                    for obj in self.level_file.objects.objects:
                        if obj.objectid == 5003:  # TMapObjSandPillar
                            obj.position = route.points[0].position.copy()

            # An intro camera looks too bad and can do with some tweaking.
            for camera in intro_cameras:
                if similar_position(camera.position, -19108, 6673, 3243):
                    camera.rotation.rotate_around_z(3)
                    camera.position2.y = 3100
                    camera.position2.z = -7700
                    camera.position3.y = 8000
                    camera.position3.z = 900
            for route in self.level_file.routes:
                if similar_position(route.points[0].position, 18577, 7842, -22325):
                    route.points[0].position.x = 11103
                    route.points[0].position.y = 11000
                    route.points[0].position.z = 20565
                    route.points[1].position.y = 8000

            set_drift(-25178, 5427, -20962, 0, 0, 0)     # Move...
            set_drift(-11860, 4937, -27092, 1, 180, 90)  # ...with some tweaks.
            set_drift(12653, 5196, -28575, 0, 0, 0)     # Move...
            set_drift(18209, 5840, -24664, 1, 20, 110)  # ...with some tweaks.
            move_drift(-19287, 4333, 16476, -26016, 5655, 8536)

            move_swerve(-23817, 5364, -25166, -14887, 5328, -28504)
            move_swerve(-7999, 4544, -23456, -5970, 4392, -23690)
            move_swerve(-2780, 4144, -26529, 934, 4146, -26011)
            move_swerve(2222, 4264, -23894, 7203, 4666, -24840)
            move_swerve(10979, 5004, -28295, 18209, 5840, -24664)
            move_swerve(15961, 5132, -13920, 14950, 5009, -2195)
            move_swerve(20551, 5150, -13871, 21265, 5033, -2122)
            move_swerve(15421, 5794, 12472, 11904, 5841, 16523)
            move_swerve(15698, 5775, 12312, 12258, 5870, 16363)
            move_swerve(-24047, 5407, 4497, -24386, 5319, -154)
            move_swerve(-23680, 5023, 15222, -26091, 5647, 12610)

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

            # Reverse car routes. First segments remains as-is (with some tweaks); the rest is
            # reversed.
            route0 = self.level_file.routes[0].points
            route1 = self.level_file.routes[1].points
            self.level_file.routes[0].points = route1[0:12] + list(reversed(route0[13:]))
            self.level_file.routes[1].points = route0[0:13] + list(reversed(route1[12:]))
            self.level_file.routes[0].points[10].position.x = 24090.082
            self.level_file.routes[0].points[10].position.z = 13403.824
            self.level_file.routes[0].points[11].position.x = 23538.855
            self.level_file.routes[0].points[11].position.z = 12792.097
            self.level_file.routes[1].points[12].position.x = 24614.918
            self.level_file.routes[1].points[12].position.z = 12348.223

        elif Course.MarioCircuit:
            # Last item boxes are not too useful in the last lap. They will be moved a few curves
            # ahead.
            for obj in self.level_file.objects.objects:
                a = type(obj.position)(-1110, 1174, 13390)
                b = type(obj.position)(-1355, 1115, 15357)
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

                # Reorient dancing cactus.
                if obj.objectid == 3711:  # GeoKuribo
                    obj.rotation.rotate_around_z(pi)

                # Trees need to be rotated too.
                if similar_position(obj.position, 2891, 1217, 19479):
                    obj.rotation.rotate_around_z(1.0)
                elif similar_position(obj.position, 5245, 1623, 20018):
                    obj.rotation.rotate_around_z(1.2)
                elif similar_position(obj.position, 10587, 2858, 21940):
                    obj.rotation.rotate_around_z(0.9)

            move_drift(9182, 1745, -25706, 3127, 1338, -23933)
            set_drift(-3429, 1118, 16327, 0, 0, 0)   # Move...
            set_drift(638, 1103, 17492, 1, 20, 110)  # ...with tweaks.
            move_drift(-13441, 1100, 20407, -4988, 1100, 20553)

            set_swerve(-12062, 1100, -12846, 0)
            set_swerve(-7421, 1100, -12574, 0)
            set_swerve(-3859, 1118, -14237, 0)
            set_swerve(-13880, 1100, -11806, 1)
            set_swerve(-12062, 1100, -12846, 1)
            set_swerve(-9196, 1100, -12506, -2)
            set_swerve(-7421, 1100, -12574, -1)
            set_swerve(-5636, 1100, -13771, 1)
            move_swerve(3799, 1192, -17946, 3077, 1170, -16319)
            move_swerve(9182, 1745, -25706, 3127, 1338, -23933)
            move_swerve(10654, 3109, 237, 9748, 3067, -2882)
            set_swerve(12380, 3065, 6983, 0)  # Move...
            set_swerve(12348, 3121, 3108, 2)  # ...with tweaks.
            set_swerve(12742, 3095, 5021, 1)
            set_swerve(11292, 2955, 9528, -2)
            set_swerve(10681, 2840, 11428, -1)
            set_swerve(10863, 2838, 13444, 0)
            set_swerve(12839, 3303, 17138, 1)
            move_swerve(-3429, 1118, 16327, 638, 1103, 17492)
            move_swerve(-13441, 1100, 20407, -4203, 1103, 18653)

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
                    # working, which is interesting, considering that the other swimming pool
                    # (0x0F01_0x01_0x000001FF) did not require this splash object for some reason,
                    # as if 0xFF was a wildcard. The index of this new splash object (1) matches the
                    # second-to-last byte in the material label of the new pool
                    # (0x0F00_0x01_0x00000101).
                    splash_obj = libbol.MapObject.new()
                    # Route Point ID, -1 as in all the other known GeoSplash objects.
                    splash_obj.unk_2a = -1
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
                    next_enemy_point = 60
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

            # Move the enemy points further away from the sinkhole.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, 8542, 6500, -3127):
                    point.position.x = 8142.213
                    point.position.z = -3127.079
                elif similar_position(point.position, 8089, 6500, -1186):
                    point.position.x = 7789.159
                    point.position.z = -1186.135
                elif similar_position(point.position, 7559, 6500, 502):
                    point.position.x = 8059.327
                    point.position.z = 502.164
                elif similar_position(point.position, 7049, 6500, 2036):
                    point.position.x = 7549.738
                    point.position.z = 2136.31
                elif similar_position(point.position, 5849, 6500, 2726):
                    point.position.x = 5849.263
                    point.position.z = 2726.01
                elif similar_position(point.position, 4145, 6500, 2649):
                    point.position.x = 4145.449
                    point.position.z = 2599.426
                elif similar_position(point.position, -78, 6419, 2568):
                    point.position.x = 1105.2
                    point.position.z = 2632.4

            for point in self.level_file.enemypointgroups.points():
                # Some points after the first big U-turn were too accented.
                if similar_position(point.position, 26300, 7250, -4370):
                    point.position.x = 25992.0
                    point.position.z = -4766.0
                elif similar_position(point.position, 22650, 7294, -5700):
                    point.scale = 1500
                # And the points before the stairs need to be tweaked, or else karts can end up in
                # the cone at the back.
                elif similar_position(point.position, -24535, 6500, 5529):
                    point.position.z = 5783.759
                elif similar_position(point.position, -26487, 6500, 5437):
                    point.position.x = -26929.496
                    point.position.z = 5922.057
                elif similar_position(point.position, -29155, 6500, 5463):
                    point.position.z = 5950.166
                elif similar_position(point.position, -31115, 6500, 5386):
                    point.position.x = -31667.016
                    point.position.z = 5958.966
                elif similar_position(point.position, -34501, 6500, 4974):
                    point.position.x = -34869.266
                    point.position.z = 5122.197
                elif similar_position(point.position, -37110, 6500, 3832):
                    point.position.x = -37221.115
                    point.position.z = 3574.838
                elif similar_position(point.position, -38264, 6500, 1459):
                    point.position.x = -38521.682
                    point.position.z = 1091.93
                    point.scale = 11000

                # Last straight segment needs to be tweaked to avoid a idiotic hit on a all.
                elif similar_position(point.position, -3847, 9244, -5151):
                    point.position.x = -3472
                    point.position.z = -4668
                elif similar_position(point.position, -920, 9000, -3651):
                    point.position.x = -974.038
                    point.position.z = -3383.619

            move_drift(29225, 7250, -3800, 30650, 7250, 3200)
            set_drift(-2888, 6500, -595, 1, 10, 100)

            move_swerve(17432, 8289, 4218, 12046, 9000, 2673)
            set_swerve(29225, 7250, -3800, 0)
            set_swerve(25992, 7250, -4766, 0)
            set_swerve(9978, 6500, -3951, -2)
            swap_swerve(5849, 6500, 2726, 7549, 6500, 2136)
            move_swerve(4145, 6500, 2599, 8059, 6500, 502)
            set_swerve(-1415, 6500, 2016, 1)
            set_swerve(-2332, 6500, 836, 0)
            set_swerve(-3289, 6500, -2617, -2)
            set_swerve(-6373, 6499, -2849, 0)
            set_swerve(-8244, 6499, -3617, 0)
            set_swerve(-3472, 9244, -4668, 2)

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

            # Dancing road signs need to be reoriented and tweaked.
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, 26006, 1459, 2043):
                    obj.position.x = 27372
                    obj.position.z = -2104
                    obj.rotation.rotate_around_z(pi + 0.99)
                elif similar_position(obj.position, 27121, 1445, 360):
                    obj.rotation.rotate_around_z(pi)
                elif similar_position(obj.position, 15003, 2711, -13767):
                    obj.position.x = 13979
                    obj.position.z = -13767
                    obj.rotation.rotate_around_z(pi + 0.25)
                elif similar_position(obj.position, 12716, 2628, -13380):
                    obj.position.x = 12326
                    obj.position.z = -13136
                    obj.rotation.rotate_around_z(pi + 0.15)
                elif similar_position(obj.position, 14211, 2168, 9480):
                    obj.position.x = 13437
                    obj.position.z = 10854
                    obj.rotation.rotate_around_z(pi - 0.4)
                elif similar_position(obj.position, 13075, 2183, 11301):
                    obj.position.x = 11579
                    obj.position.z = 12357
                    obj.rotation.rotate_around_z(pi - 0.5)
                elif similar_position(obj.position, -19373, 2207, 11928):
                    obj.position.x = -19637
                    obj.position.z = 11645
                    obj.rotation.rotate_around_z(pi - 0.2)
                elif similar_position(obj.position, -20800, 2287, 10666):
                    obj.position.x = -21118
                    obj.position.z = 9635
                    obj.rotation.rotate_around_z(pi - 0.3)
                elif similar_position(obj.position, -24259, 2148, -4969):
                    obj.position.x = -23369
                    obj.position.z = -6820
                    obj.rotation.rotate_around_z(pi - 0.4)
                elif similar_position(obj.position, -22889, 2138, -7439):
                    obj.position.x = -21319
                    obj.position.z = -8484
                    obj.rotation.rotate_around_z(pi - 0.5)
                elif similar_position(obj.position, 5357, 1995, -3928):
                    obj.position.x = 6175
                    obj.position.y = 2200
                    obj.position.z = -4580
                    obj.rotation.rotate_around_z(pi + 0.25)
                elif similar_position(obj.position, 7282, 2491, -9505):
                    obj.position.x = 6962
                    obj.position.y = 2200
                    obj.position.z = -6244
                    obj.rotation.rotate_around_z(pi - 0.4)
                elif similar_position(obj.position, 6067, 2348, -11546):
                    obj.rotation.rotate_around_z(pi)
                elif similar_position(obj.position, -7376, 1443, -14242):
                    obj.position.x = -8625
                    obj.position.z = -13713
                    obj.rotation.rotate_around_z(pi + 0.4)
                elif similar_position(obj.position, -9074, 1456, -13288):
                    obj.position.x = -9755
                    obj.position.z = -12493
                    obj.rotation.rotate_around_z(pi + 0.5)
                elif similar_position(obj.position, -10092, 1979, -839):
                    obj.position.x = -7186
                    obj.position.z = 1995
                    obj.rotation.rotate_around_z(pi + 1)
                elif similar_position(obj.position, -9078, 1986, 842):
                    obj.rotation.rotate_around_z(pi)

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
                # Cosmetic tweak in the one near the big muddy sand.
                elif similar_position(point.position, -20674, 997, -4303):
                    point.position.x = -21401.741
                    point.position.z = -4707.233
                    point.rotation.rotate_around_z(-1.0)

            # Enemy points at the deepened segment are adjusted in height.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, 12947, 1242, -6231):
                    point.position.y = 1035.275
                elif similar_position(point.position, 12877, 686, -2924):
                    point.position.y = -146.868
                elif similar_position(point.position, 12947, 1242, -6231):
                    point.position.y = 959.507

            for point in self.level_file.enemypointgroups.points():
                # Some tweaks near the snakes, to make it less awkward.
                if similar_position(point.position, -2608, 1071, 11167):
                    point.position.z = 10852.944
                elif similar_position(point.position, -7295, 1682, 12188):
                    point.position.z = 11663.21
                elif similar_position(point.position, -9965, 1405, 11921):
                    point.position.z = 11643.297
                elif similar_position(point.position, -15079, 1000, 10465):
                    point.position.x = -15079.892
                    point.position.z = 11047.922
                elif similar_position(point.position, -17260, 1014, 9637):
                    point.position.x = -17769.76
                    point.position.z = 10292.955
                elif similar_position(point.position, -19495, 1010, 7963):
                    point.position.x = -19713.939
                    point.position.z = 7891.166
                # Tweak to avoid getting into the big muddy sand.
                if similar_position(point.position, -19927, 1000, 3958):
                    point.position.x = -20292.757
                elif similar_position(point.position, -20036, 980, -155):
                    point.position.x = -20901.0

            move_drift(18981, 1000, -5577, 18579, 1000, -212)
            set_drift(-15929, 997, -5665, 0, 0, 0)    # Move...
            set_drift(-20901, 980, -155, 2, 20, 150)  # ...with some tweaks.

            move_swerve(17171, 1002, -6262, 18981, 1000, -5577)
            move_swerve(13111, 1086, -9100, 16225, 1050, -8143)
            set_swerve(-17769, 1014, 10292, 1)
            set_swerve(-19713, 1010, 7891, 0)
            set_swerve(-20901, 980, -155, 0)
            swap_swerve(1397, 998, -4968, 3502, 990, -5919)
            swap_swerve(-6289, 1000, -9605, -7848, 1000, -8062)
            swap_swerve(-6573, 1000, -944, -8092, 1000, -3868)

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

            # Move the snowmen so they don't land behind trees or in downhills.
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, 16065, 2060, 21836):
                    obj.position = type(obj.position)(22311, 1876, 27388)
                elif similar_position(obj.position, 22887, 2293, 16913):
                    obj.position = type(obj.position)(15546, 1775, 17324)
                elif similar_position(obj.position, 22887, 2244, 18372):
                    obj.position = type(obj.position)(23853, 2343, 21198)

            for point in self.level_file.enemypointgroups.points():
                # Near the stalactites in the cave, points needs to be tweak, or else kart hit the
                # stalactites in the middle.
                if similar_position(point.position, 12120, 2110, -4574):
                    point.position.x = 11755
                    point.scale = 600
                elif similar_position(point.position, 10970, 2000, -2914):
                    point.position.x = 10462.054
                    point.position.z = -3169.393
                elif similar_position(point.position, 11192, 1588, -381):
                    point.position.x = 10090.304
                    point.position.z = -890.42
                elif similar_position(point.position, 12095, 1678, -1826):
                    point.position.x = 12205.4
                    point.position.z = -1669.0
                elif similar_position(point.position, 11705, 1484, -2):
                    point.position.x = 11967.104
                    point.position.z = -117.62

            for obj in self.level_file.objects.objects:
                # Ice blocks.
                if similar_position(obj.position, -5692, 1517, 9857):
                    obj.rotation.rotate_around_z(pi)
                elif similar_position(obj.position, -4277, 1517, 13086):
                    obj.rotation.rotate_around_z(3.3)
                elif similar_position(obj.position, -6400, 1517, 15595):
                    obj.rotation.rotate_around_z(2.0)
                elif similar_position(obj.position, 336, 1521, 16536):
                    obj.rotation.rotate_around_z(-2.1)
                elif similar_position(obj.position, 3130, 1517, 18294):
                    obj.rotation.rotate_around_z(-2.2)
                elif similar_position(obj.position, 3271, 1521, 23621):
                    obj.rotation.rotate_around_z(2.2)
                elif similar_position(obj.position, 8253, 1521, 22019):
                    obj.rotation.rotate_around_z(-2.4)
                elif similar_position(obj.position, 7184, 1521, 26387):
                    obj.rotation.rotate_around_z(2.0)

            move_drift(19391, 1561, 20204, 14501, 1521, 25645)
            move_drift(11049, 712, 8374, 12624, 1121, 13122)
            move_drift(20487, 1490, -11339, 17212, 1602, -4303)

            move_swerve(-2884, 1517, 16578, -4630, 1517, 14477)
            move_swerve(1829, 1521, 18980, -286, 1520, 17573)
            move_swerve(19875, 1531, 22731, 17385, 1521, 25778)
            move_swerve(19083, 1590, 17633, 19391, 1561, 20204)
            move_swerve(17223, 1371, 13140, 18619, 1518, 14989)
            move_swerve(9886, 918, 10338, 10527, 1002, 12486)
            move_swerve(12959, 671, 4507, 12288, 592, 6563)
            set_swerve(14174, 1647, -3571, 0)
            set_swerve(12205, 1678, -1669, 2)
            set_swerve(11967, 1484, -117, 1)
            move_swerve(11755, 2110, -4574, 10090, 1588, -890)
            move_swerve(20487, 1490, -11339, 20698, 1743, -6566)
            move_swerve(12943, 1176, -14487, 15379, 1199, -13819)
            move_swerve(386, 1176, -15909, 5065, 1176, -17616)
            move_swerve(-1502, 1330, -7658, -755, 1209, -9925)
            move_swerve(-5203, 1445, -5113, -3370, 1341, -6535)

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

            # An intro camera looks too bad and can do with some tweaking.
            for camera in intro_cameras:
                if similar_position(camera.position, 7644, 4106, -278):
                    camera.position.x = 6016.686
                    camera.position.z = 1852.31
                    camera.position3.x = 7584.0
                    camera.position3.z = -7105.0
                    camera.position2.x = 25879.0
                    camera.position2.z = 1367.0

            move_drift(-24648, 4000, -7710, -24500, 4100, 2405)
            move_drift(-29178, 4000, -5643, -28800, 4000, 400)

            move_swerve(11078, 4000, 13209, 8017, 4000, 8632)
            move_swerve(35957, 4430, 4000, 40176, 4000, 9464)

            # Road lights need to be reoriented and moved.
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, -8608, 4020, -10632):
                    obj.position.x = -12195.2
                    obj.position.z = -11566.8
                    obj.rotation.rotate_around_z(-pi / 2)
                elif similar_position(obj.position, -8378, 4020, -13912):
                    obj.position.x = 22906.0
                    obj.position.z = 14476.0
                    obj.rotation.rotate_around_z(pi)
                elif similar_position(obj.position, 6786, 4020, -2226):
                    obj.position.x = 6710.0
                    obj.rotation.rotate_around_z(pi / 2)
                elif similar_position(obj.position, 9153, 4020, 3377):
                    obj.position.x = 5717.0
                    obj.position.z = 1522.6
                    obj.rotation.rotate_around_z(-pi / 2)
                elif similar_position(obj.position, 27057, 4020, 12046):
                    obj.position.x = 23711.4
                    obj.position.z = 11037.2
                    obj.rotation.rotate_around_z(pi / 2)

            # Reverse car routes.
            self.level_file.routes[0].points.reverse()
            self.level_file.routes[1].points.reverse()
            self.level_file.routes[3].points.reverse()
            route2 = self.level_file.routes[2].points
            route4 = self.level_file.routes[4].points
            self.level_file.routes[2].points = route2[0:4] + list(reversed(route2[4:]))
            self.level_file.routes[4].points = route4[0:3] + list(reversed(route4[3:]))
            self.level_file.routes[2].points[2].position.z = 7140
            self.level_file.routes[2].points[3].position.z = 7500
            self.level_file.routes[4].points[2].position.x = 16864.784

        elif Course.YoshiCircuit:
            for point in self.level_file.respawnpoints:
                # Cosmetic tweaks for respawn points.
                if similar_position(point.position, 3018, 13860, -13285):
                    point.rotation.rotate_around_z(-1.0)
                elif similar_position(point.position, 8601, 12936, -3799):
                    point.rotation.rotate_around_z(0.4)
                # Another tweak near the finish line to prevent CPU karts falling again after
                # respawning.
                elif similar_position(point.position, -2566, 12997, 18698):
                    point.position.x = -466.27
                    point.position.z = 21580.031
                    point.rotation.rotate_around_z(-1.5)
                    point.unk1 = 102  # Next enemy point.
            # Move the last item boxes, so that the now last curve can be fun.
            for obj in self.level_file.objects.objects:
                a = type(obj.position)(-4250, 12951, 18133)
                b = type(obj.position)(-3155, 12952, 16932)
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

            # The respawn point assigned to the pond shortcut point needs to be moved further back,
            # to penalize a failed shortcut.
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
                    new_area.shape = 0  # Non-spherical
                    new_area.position.x = 3027
                    new_area.position.y = 12400 - 700
                    new_area.position.z = -16100
                    new_area.scale.x = 14.0  # 700 / 100 * 2 (700 was the radius of the cylinder).
                    new_area.scale.y = 14.0
                    new_area.scale.z = 7.0  # The depth is 700.
                    new_area.rotation = new_area.rotation.default()
                    new_area.rotation.rotate_around_z(0.262)
                    new_areas.append(new_area)

                    new_area = clone_map_area(area)
                    new_area.shape = 0  # Non-spherical
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
                    new_area.shape = 0  # Non-spherical
                    inner_cylinder_factor = 0.75
                    new_area.position.x = 3027
                    new_area.position.y = 12400 - 700 * inner_cylinder_factor
                    new_area.position.z = -16100
                    new_area.scale.x = 14.0 * inner_cylinder_factor
                    new_area.scale.y = 14.0 * inner_cylinder_factor
                    new_area.scale.z = 7.0  # The depth is 700.
                    new_area.rotation = new_area.rotation.default()
                    new_area.rotation.rotate_around_z(0.262)
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

            for point in self.level_file.enemypointgroups.points():
                # Tweaks on second curve, to avoid eating the grass after the first curve.
                if similar_position(point.position, 13054, 12705, 25221):
                    point.position.x = 13445.357
                    point.position.z = 25075.243
                elif similar_position(point.position, 12946, 12705, 23074):
                    point.position.x = 13532.05
                    point.position.z = 23220.627
                # Some points in the crest need to be tweaked (some will be removed later), to make it smoother, or else
                # things are too erratic, and the entrance too the tunnel makes it bad generally.
                elif similar_position(point.position, 7669, 12945, -7801):
                    point.position.x = 8232.261
                    point.position.z = -7903.915
                elif similar_position(point.position, 8380, 13997, -11808):
                    point.position.x = 8128.979
                    point.position.z = -11544.241
                elif similar_position(point.position, 7587, 13978, -12824):
                    point.position.x = 7175.526
                    point.position.z = -12572.723
                elif similar_position(point.position, 3913, 13866, -13459):
                    point.position.x = 4030.391
                    point.position.z = -13820.262
                elif similar_position(point.position, 2237, 13859, -14333):
                    point.position.x = 2664.441
                    point.position.z = -14450.029
                elif similar_position(point.position, 1502, 13819, -15587):
                    point.position.x = 1936.383
                    point.position.z = -15711.146
                # To avoid over-correcting a bad turn after the tunnel and landing in the water.
                elif similar_position(point.position, -6971, 12809, 1728):
                    point.position.x = -6475.546
                    point.position.z = 2224.673
                elif similar_position(point.position, -7187, 13141, 3766):
                    point.position.x = -6691.301
                    point.position.z = 4076.489
                elif similar_position(point.position, -7703, 13337, 5546):
                    point.position.x = -7269.376
                    point.position.z = 5794.168
                # Similarly, to avoid an over-corretion in a bad turn that may end in water.
                elif similar_position(point.position, -3098, 12977, 17983):
                    point.position.x = -2510.939
                    point.position.z = 17983.611
                # And, similarly, in the last turn before the finish line, another over-correction
                # could occur that could make the kart land in water.
                elif similar_position(point.position, -1380, 12935, 22768):
                    point.position.x = -1290.074
                    point.position.z = 23129.711
                elif similar_position(point.position, -2456, 12930, 23440):
                    point.position.x = -2140.189
                    point.position.z = 23892.609
                elif similar_position(point.position, -3587, 12911, 24066):
                    point.position.x = -3451.53
                    point.position.z = 24337.329

            # Near the crest, there are too many points, with too many erratic turns. Straighten it.
            del_enemy_point(7037, 12936, -1556)
            del_enemy_point(8941, 12936, -4622)

            move_drift(-5835, 12704, 31884, -4905, 12863, 24986)
            move_drift(-10930, 13195, 15985, -11722, 13079, 10613)
            set_drift(3649, 12736, 2924, 0, 0, 0)     # Move...
            set_drift(4085, 12172, 6509, 2, 15, 100)  # ...with some tweaks.
            move_drift(20910, 12705, 8373, 24225, 12705, 11514)
            move_drift(14270, 12705, 27754, 10768, 12705, 33512)

            # From start to crest.
            move_swerve(14270, 12705, 27754, 10768, 12705, 33512)
            move_swerve(13532, 12705, 23220, 13445, 12705, 25075)
            move_swerve(20910, 12705, 8373, 24225, 12705, 11514)
            move_swerve(15567, 12705, 9745, 18676, 12705, 9348)
            move_swerve(2776, 12452, 3478, 2837, 12161, 6117)

            # Crest.
            move_swerve(6007, 12936, 2045, 4882, 12922, 2765)
            set_swerve(8232, 12945, -7903, 0)
            move_swerve(6098, 13950, -13313, 8635, 13914, -10153)
            move_swerve(1936, 13819, -15711, 6098, 13950, -13313)
            move_swerve(-4229, 13483, -19254, -393, 13658, -18786)
            move_swerve(-7297, 13289, -15353, 1936, 13819, -15711)

            # Tunnel.
            move_swerve(-10108, 13219, -12035, -7845, 13282, -13505)
            move_swerve(-11028, 12743, -428, -11655, 13179, -12080)
            move_swerve(-6475, 12809, 2224, -9313, 12746, -451)

            # From tunnel to end.
            move_swerve(-10367, 13064, 9834, -8362, 13307, 7398)
            move_swerve(-10930, 13195, 15985, -11722, 13079, 10613)
            move_swerve(-5243, 12854, 16345, -8093, 12903, 15838)
            move_swerve(-1290, 12935, 23129, -1119, 12989, 20140)
            move_swerve(-4313, 12704, 33188, -4905, 12863, 24986)

        elif Course.DKMountain:
            # Remove enemy point group in the old cliff shortcut. Red shells cannot follow it.
            for point in list(self.level_file.enemypointgroups.groups[2].points):
                # Use helper function to ensure next enemy point in respawn points are shifted.
                del_enemy_point(point.position.x, point.position.y, point.position.z)
            del self.level_file.enemypointgroups.groups[2]
            # Reassign group IDs.
            self.level_file.enemypointgroups._group_ids = {}
            for i, group in enumerate(self.level_file.enemypointgroups.groups):
                group.id = i
                self.level_file.enemypointgroups._group_ids[i] = group
                for point in group.points:
                    point.group = i
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
                    next_enemy_point = 73
                    point.unk1 = next_enemy_point
                    point.position.x = -12391.407
                    point.position.y = 10500
                    point.position.z = 13793.222
                    point.rotation.rotate_around_z(0.2)
            # Enemy points towards the barrel cannon need to be more strict (less scale factor), or
            # else CPU karts can get stuck against the metallic fence.
            del_enemy_point(111, 33802, -59231)
            del_enemy_point(400, 33791, -60900)
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, -253, 33824, -57218):
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
                    next_enemy_point = 72
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
                a = type(obj.position)(-19352, 8480, 20529)
                b = type(obj.position)(-18799, 8463, 19630)
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
                    point.rotation.rotate_around_z(0.1)
                elif similar_position(point.position, -11801, 7500, -16852):
                    point.position.x = -11505.857
                    point.position.y = 7500.582
                    point.position.z = -16181.864
                    point.rotation.rotate_around_z(pi / 1.9)
                elif similar_position(point.position, -14610, 9166, -28576):
                    point.rotation.rotate_around_z(-pi / 2)
                elif similar_position(point.position, 10505, 20014, -38217):
                    point.rotation.rotate_around_z(pi / 2)
            # A new enemy point needs to be added near the cliff, for the karts that fall from the
            # upper level.
            new_respawn_point = libbol.JugemPoint.new()
            new_respawn_point.position.x = -8800.237
            new_respawn_point.position.y = 8598.979
            new_respawn_point.position.z = -21805.806
            new_respawn_point.rotation.rotate_around_z(1.7)
            new_respawn_point.respawn_id = 8
            new_respawn_point.unk1 = 19  # Next enemy point.
            new_respawn_point.unk2 = -1
            new_respawn_point.unk3 = -1
            self.level_file.respawnpoints.append(new_respawn_point)
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

            for point in self.level_file.enemypointgroups.points():
                # Enemy points near the snake turns need to be tweaked (first two turns), or else
                # karts can end up in the abysm.
                if similar_position(point.position, -14500, 7480, -22900):
                    point.position.x = -15270.958
                    point.position.z = -22900.0
                elif similar_position(point.position, -12606, 7551, -22400):
                    point.position.x = -13955.122
                    point.position.z = -23717.907
                elif similar_position(point.position, -12455, 7452, -21150):
                    point.position.x = -12755.841
                    point.position.z = -20865.825
                elif similar_position(point.position, -12455, 7412, -19899):
                    point.position.x = -12645.24
                    point.position.z = -19547.395
                elif similar_position(point.position, -12237, 7402, -18537):
                    point.position.x = -12538.038
                    point.position.z = -18174.102
                elif similar_position(point.position, -11887, 7479, -17105):
                    point.position.x = -11931.155
                    point.position.z = -16402.443
                elif similar_position(point.position, -10630, 7728, -16693):
                    point.position.x = -10565.575
                    point.position.z = -16210.289
                elif similar_position(point.position, -11100, 9129, -26004):
                    point.position.x = -11100.0
                    point.position.z = -25826.309
                elif similar_position(point.position, -12200, 9162, -26700):
                    point.position.x = -12361.0
                    point.position.z = -26470.0
                # Some rather costmetic tweaks during the ascent, or else karts skip the item boxes
                # in the road.
                elif similar_position(point.position, -6918, 12521, -31247):
                    point.position.x = -7266.344
                    point.position.z = -31247.717
                elif similar_position(point.position, -7423, 14182, -33071):
                    point.position.x = -7818.573
                    point.position.z = -33071.27
                elif similar_position(point.position, -6533, 15394, -34471):
                    point.position.x = -6991.471
                    point.position.z = -34581.905

            # Remove some enemy points towards the finish line, to straighten the path a bit, or
            # else karts have a very bad entrance in the bridge.
            del_enemy_point(-15095, 6307, 10178)
            del_enemy_point(-15633, 5709, 8856)
            del_enemy_point(-16438, 4804, 6542)
            del_enemy_point(-16326, 4521, 5641)

            set_drift(-10859, 9238, -29607, 0, 0, 0)     # Move...
            set_drift(-12361, 9162, -26470, 2, 20, 120)  # ...with some tweaks.
            move_drift(-5428, 11686, -30140, -7105, 10326, -26493)

            # First snake turns.
            set_swerve(-15622, 7253, -20629, 0)
            move_swerve(-9499, 8100, -18018, -12538, 7402, -18174)
            set_swerve(-9499, 8100, -18018, 1)

            # Last big curve after landing.
            set_swerve(-20500, 8414, 18500, 1)
            set_swerve(-20900, 8304, 16700, 2)

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
                    point.position.x = -6059.032
                    point.position.z = -12696.782
                    point.scale = 600
                elif similar_position(point.position, -4636, 21576, -12562):
                    point.position.x = -4437.562
                    point.position.z = -12681.667
            # Cosmetic tweaks to some respawn points.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, -16658, 17269, 307):
                    respawn_point.rotation.rotate_around_z(0.10)
                elif similar_position(respawn_point.position, -1593, 20711, 9094):
                    respawn_point.rotation.rotate_around_z(0.35)
                elif similar_position(respawn_point.position, 1426, 21154, -168):
                    respawn_point.position.y = 20800  #  Avoids bouncing off the ground.
                    respawn_point.rotation.rotate_around_z(0.25)
                elif similar_position(respawn_point.position, 17125, 25365, 7093):
                    respawn_point.rotation.rotate_around_z(0.15)

            for point in self.level_file.enemypointgroups.points():
                # Enemy point in the first snail ascent, after the boost pad, can be centered a
                # little bit.
                if similar_position(point.position, -6213, 18491, 2435):
                    point.position.x = -6082.172
                    point.position.z = 2856.917
                elif similar_position(point.position, -4811, 20815, 1655):
                    point.position.x = -4653.874
                    point.position.z = 1916.698
                # Between the two snail ascents (the tricky part), some points need to be tweaked to
                # prevent karts from insta falling to the void. Others will be removed later to make
                # it more straight.
                elif similar_position(point.position, -1089, 21834, -6448):
                    point.position.x = -1187.904
                    point.position.y = 21834.662
                    point.position.z = -7288.702
                elif similar_position(point.position, -359, 21731, -7832):
                    point.position.x = -112.27
                    point.position.y = 21937.992
                    point.position.z = -8573.212
                elif similar_position(point.position, 1354, 21586, -7983):
                    point.position.x = 1898.284
                    point.position.y = 21837.668
                    point.position.z = -8526.584
                elif similar_position(point.position, 7031, 22370, -3765):
                    point.position.x = 7237.564
                    point.position.y = 22451.553
                    point.position.z = -3868.946
                elif similar_position(point.position, 7325, 22688, -2074):
                    point.position.x = 8186.436
                    point.position.y = 23243.514
                    point.position.z = -1574.911
                elif similar_position(point.position, 7065, 22986, -310):
                    point.position.x = 8029.597
                    point.position.y = 23747.464
                    point.position.z = 329.514
                elif similar_position(point.position, 1840, 21208, -136):
                    point.position.x = 3261.442
                    point.position.y = 21601.882
                    point.position.z = -205.137
                # The enemy point at the very center of the newly added cannon needs to be centered,
                # and small enough to make sure karts want to get to that point.
                elif similar_position(point.position, -196, 28815, -30):
                    point.scale = 1300
                # Some tweaks in the last jump, as karts could fall easily (without any external
                # intervention).
                elif similar_position(point.position, 4960, 23793, 11950):
                    point.position.z = 11780.2
                elif similar_position(point.position, -20, 23861, 11523):
                    point.position.x = -699.826

            # From start to the newly added boost pad in the steep slope.
            set_drift(-13600, 22179, -10077, 2, 10, 70)
            set_drift(16470, 17000, 5858, 2, 10, 80)
            move_swerve(13900, 17000, 8209, 15279, 17000, 7449)
            move_swerve(12607, 17022, 8059, 16470, 17000, 5858)
            move_swerve(-5012, 13303, -143, 2097, 13150, 4129)
            move_swerve(-1022, 13271, -4834, 5453, 13524, 906)

            # First snail ascent.
            move_swerve(-6558, 22059, -1301, -3707, 21497, -718)
            move_drift(-7918, 21914, 1915, -4653, 20815, 1916)
            set_swerve(-4653, 20815, 1916, -1)
            move_drift(-7635, 22106, -83, -3642, 21235, 565)
            swap_drift(-6558, 22059, -1301, -3707, 21497, -718)
            set_drift(-6558, 22059, -1301, 1, 50, 100)

            # Between first and second snail ascent.
            set_swerve(-6926, 21196, 5418, -1)
            set_swerve(-5717, 20673, 7054, -1)
            move_swerve(211, 21232, 8619, -2085, 20594, 8688)
            del_enemy_point(3034, 21571, -7624)
            del_enemy_point(4688, 21692, -6568)
            del_enemy_point(6158, 22002, -5144)
            del_enemy_point(5561, 22783, 827)
            del_enemy_point(3815, 21861, 184)
            set_swerve(8186, 23243, -1574, 0)
            set_swerve(8029, 23747, 329, 3)
            set_swerve(3261, 21601, -205, -1)

            # Second snail ascent.
            del_enemy_point(-1604, 21831, 1011)
            move_drift(-4345, 27449, -1636, -5072, 23678, 1409)
            move_drift(-2488, 28000, -943, -3350, 22925, 1562)
            del_enemy_point(-2488, 28000, -943)
            set_drift(-5884, 26304, 1215, 2, 20, 150)
            set_drift(-6327, 26602, 111, 0, 0, 0)
            set_drift(-5913, 26999, -1388, 0, 0, 0)
            set_drift(-196, 28815, -30, 0, 0, 0)

            # From landing area to finish line.
            move_swerve(23890, 25365, 13337, 23368, 25365, 8209)
            move_swerve(-13190, 22179, 8870, -10840, 22179, 11240)

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
            for respawn_point in self.level_file.respawnpoints:
                # Respawn point needs to be tweaked to avoid launching respawned karts to the water.
                if similar_position(respawn_point.position, -18294, 8952, 12319):
                    respawn_point.position.x = -16713.382
                    respawn_point.position.y = 8698.044
                    respawn_point.position.z = 12171.751
                    respawn_point.rotation.rotate_around_z(0.75)
                    respawn_point.unk1 = 54  # Next enemy point.
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
                elif similar_position(point.position, -4605, 12262, -11007):
                    point.position.x = -4309.077
                    point.position.z = -11452.212
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
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, -12633, 12504, -22921):
                    point.position.x = -12530.356
                    point.position.z = -23180.379
                elif similar_position(point.position, -20516, 12354, -22366):
                    point.position.x = -20685.577
                    point.position.z = -22661.964
                elif similar_position(point.position, -22043, 12226, -20509):
                    point.position.x = -22628.98
                    point.position.z = -20704.648
                # Point at the end of the cave, before the bridges, needs to be tweaked or else
                # karts try to go directly between the main bridge and the items-only bridge.
                elif similar_position(point.position, -27528, 12069, -5512):
                    point.position.x = -27498.599
                    point.position.z = -8129.775
                    point.scale = 700
                # Enemy points in the long bridge need to be adjusted as well, to guide the AI karts
                # better.
                elif similar_position(point.position, -17470, 8866, 12261):
                    point.position.x = -17435.271
                    point.position.y = 8866.754
                    point.position.z = 11946.225
                    point.scale = 800
                elif similar_position(point.position, -15751, 8561, 11559):
                    point.position.x = -15969.435
                    point.position.y = 8561.806
                    point.position.z = 11114.473
                    point.scale = 800
                elif similar_position(point.position, -14698, 8251, 9954):
                    point.position.x = -15042.951
                    point.position.y = 8251.187
                    point.position.z = 9609.563
                    point.scale = 900
                # Space out one of the enemy points in the secondary bridge (by the long bridge), to
                # avoid the issue where karts may end up following an items-only enemy point nearby.
                elif similar_position(point.position, -28089, 11961, -3098):
                    point.position.x = -28452.639
                    point.position.y = 11925.776
                    point.position.z = -2411.521
                    point.scale = 700
                # Enemy point after the dino's legs can be tweaked for a better entrance.
                elif similar_position(point.position, 6118, 8427, -7632):
                    point.position.x = 7023.245
                    point.position.z = -8284.58

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

            # Before cave.
            move_drift(7768, 10942, 11893, 11082, 10465, 11875)
            move_swerve(7768, 10942, 11893, 11082, 10465, 11875)
            move_swerve(7352, 10900, 7767, 7600, 10927, 9588)

            # Cave.
            move_swerve(-22628, 12226, -20704, -15575, 12736, -24508)
            set_swerve(-29344, 12069, -13709, -2)
            set_swerve(-29532, 12069, -11003, -3)
            set_swerve(-28176, 12069, -9351, 1)
            del_enemy_point(-27683, 12069, -7870)

            # Bridges.
            set_swerve(-24400, 10341, 8258, -2)
            set_swerve(-23092, 9692, 10347, -2)
            set_swerve(-19378, 9115, 12218, -3)
            set_swerve(-17435, 8866, 11946, -3)

            # After dino legs.
            set_swerve(-2440, 8138, 3184, 0)
            set_swerve(340, 8140, 2737, -1)
            move_swerve(8232, 8427, -12960, 7957, 8422, -9905)
            move_drift(11884, 8427, -17685, 6694, 8427, -15462)

        elif Course.BowsersCastle:
            # Remove enemy point group in the old cliff shortcut. Red shells cannot follow it.
            for point in list(self.level_file.enemypointgroups.groups[2].points):
                # Use helper function to ensure next enemy point in respawn points are shifted.
                del_enemy_point(point.position.x, point.position.y, point.position.z)
            del self.level_file.enemypointgroups.groups[2]
            # Reassign group IDs.
            self.level_file.enemypointgroups._group_ids = {}
            for i, group in enumerate(self.level_file.enemypointgroups.groups):
                group.id = i
                self.level_file.enemypointgroups._group_ids[i] = group
                for point in group.points:
                    point.group = i
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
                    respawn_point.unk1 = 23  # Next enemy point.
            # Another respawn point too close to a cliff near the metallic platform with a hole.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, -11688, 5856, -12973):
                    respawn_point.position.x = -11723.361
                    respawn_point.position.y = 6028.209
                    respawn_point.position.z = -18417.947
                    respawn_point.unk1 = 93  # Next enemy point.
                    respawn_point.unk3 = 52  # Preceding checkpoint.
            # A respawn point that needs to be rotated as it's facing a wall, and aligned with the
            # carpet.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, -3153, 9010, 15136):
                    respawn_point.position.x = -3093.5
                    respawn_point.position.z = 15757.868
                    respawn_point.rotation.rotate_around_z(-pi / 2)
            # A couple of respawn points need to be rotated slightly, as they are rather facing to
            # the lava again.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, -30462, 8116, 17398):
                    respawn_point.position.x = -30606.455
                    respawn_point.position.y = 8417.531
                    respawn_point.position.z = 16155.891
                    respawn_point.rotation.rotate_around_z(-0.8)
                    respawn_point.unk1 = 17  # Next enemy point.
                elif similar_position(respawn_point.position, -30371, 8132, 17941):
                    respawn_point.position.x = -27975.016
                    respawn_point.position.y = 8581.893
                    respawn_point.position.z = 15080.763
                    respawn_point.rotation.rotate_around_z(-2.4)
                    respawn_point.unk1 = 18  # Next enemy point.
            # Some enemy points need to be slightly replaced, or else the AI karts can be too dumb
            # against walls.
            for point in self.level_file.enemypointgroups.points():
                # First curve after start line.
                if similar_position(point.position, 3535, 8100, 19999):
                    point.position.x = 3785.565
                    point.position.z = 19666.548
                elif similar_position(point.position, 3188, 8100, 22929):
                    point.position.x = 3812.363
                    point.position.z = 22513.338
                elif similar_position(point.position, 1997, 8100, 24023):
                    point.position.x = 1537.193
                    point.position.z = 24003.422
                elif similar_position(point.position, -570, 8141, 24697):
                    point.position.x = -590.0
                    point.position.z = 24497.0
                # In the castle before snail descent.
                elif similar_position(point.position, -12131, 9010, 4542):
                    point.position.x = -12086.745
                    point.position.z = 2593.915
                elif similar_position(point.position, -11369, 9010, 4548):
                    point.position.x = -11616.287
                    point.position.z = 2593.915
                elif similar_position(point.position, -11844, 9000, 2623):
                    point.position.x = -11844.703
                    point.position.z = 1023.955
                # After the snail descent.
                elif similar_position(point.position, -11712, 5850, -11443):
                    point.position.z = -9678.962
                elif similar_position(point.position, -12694, 5850, -13424):
                    point.position.x = -12818.199
                    point.position.z = -13424.899
                elif similar_position(point.position, -10821, 5850, -13424):
                    point.position.x = -10425.099
                    point.position.z = -13424.899
                # Before the two corridors.
                elif similar_position(point.position, 2229, 6937, -25547):
                    point.position.x = 1947.2
                    point.position.z = -26168.349
                elif similar_position(point.position, 2265, 6937, -17314):
                    point.position.x = 2485.527
                    point.position.z = -19180.256
                    point.scale = 700
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
                elif similar_position(point.position, -26565, 8765, 18414):
                    point.position.x = -26245.17
                    point.position.z = 19054.062
                elif similar_position(point.position, -26336, 8799, 19723):
                    point.position.x = -25607.068
                    point.position.z = 20999.697
                elif similar_position(point.position, -24785, 8829, 21205):
                    point.position.x = -24306.474
                    point.position.z = 21910.097
                elif similar_position(point.position, -21764, 8829, 21243):
                    point.position.x = -22101.443
                    point.position.z = 22001.798
                    point.scale = 1000
                elif similar_position(point.position, -19036, 8829, 21244):
                    point.position.x = -19105.667
                    point.position.z = 21906.953
                elif similar_position(point.position, -24457, 8829, 22795):
                    point.position.x = -24072.8
                    point.position.z = 22455.299
            # The old area (type 5) that was present in the last jump needs to be removed as there
            # is no jump anymore. (At this point, it is not fully known what these area types mean,
            # but they always appear in jumps.)
            for area in list(self.level_file.areas.areas):
                if similar_position(area.position, -7263, 6057, 25103):
                    self.level_file.areas.areas.remove(area)
                    break

            for obj in self.level_file.objects.objects:
                # Reorient falling blocks.
                if obj.objectid == 4701:  # TMapObjDossun
                    obj.rotation.rotate_around_z(pi)

            # Move last item boxes further from the finish line.
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, 2634, 6937, -6847):
                    obj.position = type(obj.position)(2573, 6930, -19643)
                elif similar_position(obj.position, 3084, 6937, -6847):
                    obj.position = type(obj.position)(3070, 6930, -19364)
                elif similar_position(obj.position, 4038, 6937, -6847):
                    obj.position = type(obj.position)(4099, 6930, -19364)
                elif similar_position(obj.position, 4515, 6937, -6847):
                    obj.position = type(obj.position)(4662, 6930, -19643)

            # From start to the stairs.
            set_swerve(3785, 8100, 19666, 0)
            set_swerve(3812, 8100, 22513, 3)
            set_swerve(1537, 8100, 24003, 1)
            del_enemy_point(-24777, 8739, 24972)
            set_swerve(-27622, 8331, 24955, 1)
            del_enemy_point(-31052, 8108, 19852)
            set_swerve(-26717, 8730, 17217, 0)
            set_swerve(-26245, 8765, 19054, -1)

            # Between stairs and before the snail descent.
            move_swerve(-7561, 11700, 14330, -4987, 11700, 16750)
            set_drift(-7737, 11700, 10357, 0, 0, 0)
            set_drift(-4007, 10291, 7524, 0, 0, 0)
            set_drift(-8065, 10822, 6015, 2, 10, 130)
            del_enemy_point(-7899, 11313, 8126)
            set_swerve(-8065, 10822, 6015, 0)
            set_swerve(-4665, 10800, 4955, 0)
            del_enemy_point(-4044, 9900, 9208)
            del_enemy_point(-3313, 9900, 10468)
            set_swerve(-11680, 9000, 12895, 0)
            set_swerve(-11844, 9000, 1023, 0)

            # Snail descent.
            swap_drift(-9686, 8153, -5870, -9278, 6925, -145)
            swap_drift(-9278, 6925, -145, -11277, 8337, -4763)
            swap_drift(-7983, 7974, -5904, -7633, 7143, -310)
            swap_drift(-6483, 7764, -4905, -6326, 7352, -1444)
            set_swerve(-11071, 6659, -1123, 0)
            del_enemy_point(-11704, 6378, -3558)
            del_enemy_point(-11690, 6350, -6038)
            del_enemy_point(-11711, 6213, -9293)

            # After snail decent before two corridors.
            set_swerve(-11712, 5850, -9678, 0)
            move_swerve(-12341, 6273, -19609, -12818, 5850, -13424)
            move_swerve(-10988, 6273, -19606, -10425, 5850, -13424)
            set_swerve(-11359, 6930, -24234, 2)
            set_swerve(3644, 6937, -23567, 0)

            # After the two corridors.
            del_enemy_point(3587, 6757, 2983)
            del_enemy_point(3575, 7002, 5157)

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
            # Enemy point before the cannon shot needs to be moved down to the ground.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, 5738, 68291, 3598):
                    point.position.y = 64415.367
                elif similar_position(point.position, 8162, 65583, 7066):
                    point.position.y = 65074.176
            # Some curves are too sharp for the AI in reverse; they need to be smoothened.
            for point in self.level_file.enemypointgroups.points():
                # After landing.
                if similar_position(point.position, 19875, 4392, 24030):
                    point.position.x = 19871.309
                    point.position.z = 22796.118
                    point.scale = 1600
                elif similar_position(point.position, 20176, 4409, 26006):
                    point.position.x = 20444.041
                    point.position.z = 26166.851
                    point.scale = 1200
                elif similar_position(point.position, 18582, 4532, 27035):
                    point.position.x = 18957.739
                    point.position.z = 27035.482
                    point.scale = 1200
                # Tiny snake turns.
                elif similar_position(point.position, 16228, 4806, 27090):
                    point.position.x = 16228.193
                    point.position.z = 27090.387
                    point.scale = 1100
                elif similar_position(point.position, 14143, 5130, 27341):
                    point.position.x = 13981.014
                    point.position.z = 27509.902
                    point.scale = 1100
                elif similar_position(point.position, 12035, 5578, 28432):
                    point.position.x = 11688.665
                    point.position.z = 28664.941
                    point.scale = 1100
                elif similar_position(point.position, 9888, 5978, 28549):
                    point.position.x = 9728.025
                    point.position.z = 28602.795
                    point.scale = 1100
                elif similar_position(point.position, 7648, 6349, 27478):
                    point.position.x = 7469.984
                    point.position.z = 27620.968
                    point.scale = 1100
                elif similar_position(point.position, 5469, 7125, 27435):
                    point.position.x = 5369.341
                    point.position.z = 27664.288
                    point.scale = 1100
                elif similar_position(point.position, 3287, 8390, 28683):
                    point.position.x = 3081.368
                    point.position.z = 28699.229
                    point.scale = 1100
                elif similar_position(point.position, 974, 9862, 28837):
                    point.position.x = 759.938
                    point.position.z = 28784.281
                    point.scale = 1100
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
                    respawn_point.position.x = 6633.166
                    respawn_point.position.y = 6655.073
                    respawn_point.position.z = 26916.46
                    respawn_point.unk1 = 36  # Next enemy point.
            # AI karts need to be guided away from the fences in the uphill, or else they could get
            # stuck.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, 2367, 34102, -9713):
                    point.position.x = 2412.421
                    point.position.z = -9983.796
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
            # One enemy point in the larger snail descent is too close to the edge.
            for point in self.level_file.enemypointgroups.points():
                if similar_position(point.position, -24114, 14014, 23607):
                    point.position.x = -24346.739
                    point.position.y = 14134.0
                    point.position.z = 23607.426
            # Some cosmetic tweaks in respawn points.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, -17823, 63268, -28608):
                    respawn_point.rotation.rotate_around_z(-0.10)
            # Some respawn points need to be moved to the other end of the curve, or else karts may
            # end up following the old, wrong enemy point, or even fall again.
            for respawn_point in self.level_file.respawnpoints:
                if similar_position(respawn_point.position, 20460, 4392, 24193):
                    respawn_point.position.x = 19596.764
                    respawn_point.position.y = 4409.465
                    respawn_point.position.z = 27044.962
                    respawn_point.rotation.rotate_around_z(-2.15)
                    respawn_point.unk1 = 30  # Next enemy point.
                elif similar_position(respawn_point.position, 2584, 34419, -10326):
                    respawn_point.position.x = 540.5
                    respawn_point.position.y = 34504.793
                    respawn_point.position.z = -12354.034
                    respawn_point.rotation.rotate_around_z(pi)
                    respawn_point.unk1 = 78  # Next enemy point.
                elif similar_position(respawn_point.position, -2945, 35773, -7203):
                    respawn_point.position.x = -6040.12
                    respawn_point.position.y = 37660.949
                    respawn_point.position.z = -8738.438
                    respawn_point.rotation.rotate_around_z(pi)
                    respawn_point.unk1 = 83  # Next enemy point.
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
            self.level_file.respawnpoints[2].unk3 = 55
            self.level_file.respawnpoints[3].unk3 = 48
            self.level_file.respawnpoints[4].unk3 = 39
            self.level_file.respawnpoints[5].unk3 = 36
            self.level_file.respawnpoints[6].unk3 = 33
            self.level_file.respawnpoints[7].unk3 = 29
            self.level_file.respawnpoints[8].unk3 = 25
            self.level_file.respawnpoints[9].unk3 = 23
            self.level_file.respawnpoints[10].unk3 = 21
            self.level_file.respawnpoints[11].unk3 = 19
            self.level_file.respawnpoints[12].unk3 = 13
            self.level_file.respawnpoints[13].unk3 = 10
            self.level_file.respawnpoints[14].unk3 = 61

            # Move last item boxes further from the finish line.
            for obj in self.level_file.objects.objects:
                if similar_position(obj.position, -780, 44710, -20686):
                    obj.position = type(obj.position)(-5046, 38631, -11214)
                elif similar_position(obj.position, -257, 44722, -20688):
                    obj.position = type(obj.position)(-4647, 38525, -10828)
                elif similar_position(obj.position, 268, 44731, -20689):
                    obj.position = type(obj.position)(-4248, 38412, -10442)
                elif similar_position(obj.position, 762, 44744, -20696):
                    obj.position = type(obj.position)(-3849, 38272, -10056)

            # First snail ascent.
            swap_drift(-19171, 63088, -29747, -16667, 58207, -36896)
            swap_drift(-20697, 62870, -32227, -18258, 58284, -37469)
            swap_drift(-21170, 62504, -33956, -19455, 58534, -37250)
            swap_drift(-21095, 62116, -35476, -20206, 58778, -36335)
            swap_drift(-20561, 61769, -36748, -20135, 59055, -35154)
            swap_drift(-19128, 59466, -34423, -19507, 61421, -37373)
            swap_drift(-17950, 59825, -34527, -18299, 60988, -37374)
            swap_drift(-17141, 60208, -35493, -17341, 60532, -36670)
            set_drift(-21095, 62116, -35476, 0, 0, 0)
            set_drift(-21170, 62504, -33956, 0, 0, 0)
            set_drift(-20697, 62870, -32227, 0, 0, 0)
            set_drift(-19171, 63088, -29747, 0, 0, 0)
            set_drift(-20561, 61769, -36748, 1, 50, 130)
            set_swerve(-20697, 62870, -32227, 0)
            set_swerve(-18299, 60988, -37374, 0)
            set_swerve(-20135, 59055, -35154, 0)
            set_swerve(-18258, 58284, -37469, -1)
            set_swerve(-17950, 59825, -34527, -1)
            set_swerve(-20561, 61769, -36748, -1)

            # After landing from cannon.
            set_drift(18957, 4532, 27035, 0, 0, 0)    # Move...
            set_drift(19871, 4392, 22796, 2, 10, 60)  # ...with tweaks.
            swap_swerve(19871, 4392, 22796, 18957, 4532, 27035)

            # Tiny snake turns.
            set_swerve(16228, 4806, 27090, -1)
            set_swerve(13981, 5130, 27509, 0)
            set_swerve(11688, 5578, 28664, 3)
            set_swerve(9728, 5978, 28602, 0)
            set_swerve(7469, 6349, 27620, -2)
            set_swerve(5369, 7125, 27664, 0)
            set_swerve(3081, 8390, 28699, 2)
            set_swerve(759, 9862, 28784, 0)
            set_swerve(-2025, 11405, 27634, -1)
            set_swerve(-4391, 13196, 27072, 0)

            # Spiral descent.
            set_swerve(-23573, 18468, 21014, 0)
            set_swerve(-15737, 16002, 25497, 0)
            set_swerve(-23891, 14328, 21429, 0)

            # Twin snake turns.
            set_drift(261, 34554, -12071, 0, 0, 0)
            set_swerve(2905, 34864, -11903, -2)
            set_swerve(1668, 34893, -12827, -3)
            set_swerve(261, 34554, -12071, 0)
            set_drift(-4835, 38201, -10057, 0, 0, 0)
            set_swerve(-4835, 38201, -10057, 0)
            set_swerve(-5676, 36897, -6596, 3)
            move_swerve(-1073, 47478, -24395, 191, 45391, -21934)


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
    padding = QtGui.QFontMetrics(QtGui.QFont()).height() // 2
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