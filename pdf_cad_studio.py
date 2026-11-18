import sys
import os
import math
import copy
import uuid
import pymupdf

from PySide6.QtWidgets import (
    QApplication, QMainWindow, QWidget, QVBoxLayout, QHBoxLayout,
    QToolBar, QToolButton, QPushButton, QLabel, QComboBox, QCheckBox,
    QListWidget, QListWidgetItem, QSplitter, QFileDialog, QMessageBox,
    QColorDialog, QInputDialog, QAbstractItemView, QMenu, QStatusBar
)
from PySide6.QtCore import Qt, QPointF, QRectF, QSize, QTimer, Signal
from PySide6.QtGui import (
    QPainter, QPen, QBrush, QColor, QPixmap, QImage, QFont,
    QPolygonF, QKeySequence, QShortcut, QIcon, QFontMetrics
)

PT_TO_MM = 25.4 / 72.0
MM_TO_PT = 72.0 / 25.4
GRID_STEP_PT = 5.0 * MM_TO_PT


def find_vietnamese_font():
    candidates = [
        r"C:\Windows\Fonts\arial.ttf",
        r"C:\Windows\Fonts\segoeui.ttf",
        r"C:\Windows\Fonts\tahoma.ttf",
        "/usr/share/fonts/truetype/dejavu/DejaVuSans.ttf",
    ]
    for path in candidates:
        if os.path.exists(path):
            return path
    return None


def format_length(mm_val: float, use_scale_units: bool = True) -> str:
    if use_scale_units and mm_val >= 1000.0:
        return f"{mm_val / 1000.0:.2f} m"
    return f"{mm_val:.1f} mm"


def hex_to_rgb_norm(hex_color: str):
    c = QColor(hex_color)
    return (c.redF(), c.greenF(), c.blueF())


def dist_to_segment(px, py, x1, y1, x2, y2):
    l2 = (x2 - x1) ** 2 + (y2 - y1) ** 2
    if l2 == 0:
        return math.hypot(px - x1, py - y1)
    t = ((px - x1) * (x2 - x1) + (py - y1) * (y2 - y1)) / l2
    t = max(0.0, min(1.0, t))
    return math.hypot(px - (x1 + t * (x2 - x1)), py - (y1 + t * (y2 - y1)))


class PageState:
    def __init__(self, source_type="blank", doc_id=None, src_page_index=0,
                 width_pt=595.28, height_pt=841.89, rotation=0):
        self.id = str(uuid.uuid4())
        self.source_type = source_type  # "pdf" or "blank"
        self.doc_id = doc_id
        self.src_page_index = src_page_index
        self.width_pt = width_pt
        self.height_pt = height_pt
        self.rotation = rotation
        self.shapes = []
        self.undo_stack = []
        self.redo_stack = []

    def push_undo(self):
        self.undo_stack.append(copy.deepcopy(self.shapes))
        if len(self.undo_stack) > 50:
            self.undo_stack.pop(0)
        self.redo_stack.clear()


class CadCanvasWidget(QWidget):
    statusChanged = Signal()
    thumbnailDirty = Signal()
    undoStateChanged = Signal()

    def __init__(self, main_win):
        super().__init__()
        self.main_win = main_win
        self.setMouseTracking(True)
        self.setFocusPolicy(Qt.StrongFocus)

        self.zoom = 1.0
        self.pan_x = 40.0
        self.pan_y = 40.0

        self.bg_pixmap = None
        self.render_timer = QTimer(self)
        self.render_timer.setSingleShot(True)
        self.render_timer.timeout.connect(self.render_pdf_background)

        # Pointer & interaction
        self.pointer_screen = QPointF(0, 0)
        self.pointer_inside = False
        self.pointer_pdf = QPointF(0, 0)
        self.snapped = {"x": 0.0, "y": 0.0, "type": None}

        self.is_panning = False
        self.pan_start = QPointF(0, 0)
        self.pan_orig = (0.0, 0.0)
        self.space_pressed = False
        self.shift_pressed = False

        self.draw_draft = None
        self.selected_id = None
        self.drag_action = None

    def active_page(self):
        return self.main_win.active_page()

    def screen_to_pdf(self, sx, sy):
        return ((sx - self.pan_x) / self.zoom, (sy - self.pan_y) / self.zoom)

    def pdf_to_screen(self, px, py):
        return (px * self.zoom + self.pan_x, py * self.zoom + self.pan_y)

    def fit_to_view(self):
        p = self.active_page()
        if not p:
            return
        pad = 40.0
        w = max(100, self.width())
        h = max(100, self.height())
        zx = (w - pad * 2) / p.width_pt
        zy = (h - pad * 2) / p.height_pt
        self.zoom = max(0.1, min(4.0, min(zx, zy)))
        self.pan_x = (w - p.width_pt * self.zoom) / 2.0
        self.pan_y = (h - p.height_pt * self.zoom) / 2.0
        self.render_pdf_background()
        self.update()
        self.statusChanged.emit()

    def render_pdf_background(self):
        p = self.active_page()
        if not p:
            self.bg_pixmap = None
            self.update()
            return
        if p.source_type == "blank":
            self.bg_pixmap = None
            self.update()
            return

        src_doc = self.main_win.pdf_sources.get(p.doc_id)
        if not src_doc:
            return

        dpr = self.devicePixelRatioF()
        max_dim = 3400.0
        max_scale = min(max_dim / p.width_pt, max_dim / p.height_pt)
        scale = min(max(1.2, self.zoom * dpr), max_scale)

        src_page = src_doc[p.src_page_index]
        # Temporarily apply page rotation to render
        old_rot = src_page.rotation
        if old_rot != p.rotation:
            src_page.set_rotation(p.rotation)
        pix = src_page.get_pixmap(matrix=pymupdf.Matrix(scale, scale), alpha=False)
        if old_rot != p.rotation:
            src_page.set_rotation(old_rot)

        img = QImage(pix.samples, pix.width, pix.height, pix.stride, QImage.Format_RGB888).copy()
        self.bg_pixmap = QPixmap.fromImage(img)
        self.update()

    # === SNAPPING ===
    def get_snap_points(self, s):
        pts = []
        t = s["type"]
        if t in ("line", "arrow", "dim"):
            pts.append((s["x1"], s["y1"], "endpoint"))
            pts.append((s["x2"], s["y2"], "endpoint"))
            pts.append(((s["x1"] + s["x2"]) / 2, (s["y1"] + s["y2"]) / 2, "midpoint"))
        elif t == "rect":
            x, y, w, h = s["x"], s["y"], s["w"], s["h"]
            pts.extend([(x, y, "endpoint"), (x + w, y, "endpoint"),
                        (x + w, y + h, "endpoint"), (x, y + h, "endpoint"),
                        (x + w / 2, y + h / 2, "midpoint")])
        elif t == "circle":
            cx, cy, r = s["cx"], s["cy"], s["r"]
            pts.extend([(cx, cy, "midpoint"), (cx + r, cy, "endpoint"),
                        (cx - r, cy, "endpoint"), (cx, cy + r, "endpoint"), (cx, cy - r, "endpoint")])
        elif t == "polyline":
            p_list = s["points"]
            for i, pt in enumerate(p_list):
                pts.append((pt[0], pt[1], "endpoint"))
                if i > 0:
                    pts.append(((p_list[i - 1][0] + pt[0]) / 2, (p_list[i - 1][1] + pt[1]) / 2, "midpoint"))
        return pts

    def compute_snapped(self, rx, ry, anchor=None):
        x, y, stype = rx, ry, None
        p = self.active_page()
        cfg = self.main_win

        if cfg.osnap_on and p:
            best = 10.0 / self.zoom
            for s in p.shapes:
                for sx, sy, sp_type in self.get_snap_points(s):
                    d = math.hypot(sx - rx, sy - ry)
                    if d < best:
                        best = d
                        x, y, stype = sx, sy, sp_type
            if self.draw_draft and self.draw_draft["type"] == "polyline" and len(self.draw_draft["points"]) >= 2:
                st = self.draw_draft["points"][0]
                if math.hypot(st[0] - rx, st[1] - ry) < best:
                    x, y, stype = st[0], st[1], "endpoint"

        if stype is None and cfg.grid_on:
            x = round(x / GRID_STEP_PT) * GRID_STEP_PT
            y = round(y / GRID_STEP_PT) * GRID_STEP_PT
            stype = "grid"

        ortho_active = cfg.ortho_on != self.shift_pressed
        if ortho_active and anchor is not None:
            if abs(x - anchor[0]) >= abs(y - anchor[1]):
                y = anchor[1]
            else:
                x = anchor[0]

        return {"x": x, "y": y, "type": stype}

    # === HIT TESTING & GEOMETRY ===
    def get_handles(self, s):
        t = s["type"]
        if t in ("line", "arrow", "dim"):
            return [(s["x1"], s["y1"]), (s["x2"], s["y2"])]
        if t == "rect":
            return [(s["x"], s["y"]), (s["x"] + s["w"], s["y"] + s["h"])]
        if t == "circle":
            return [(s["cx"] + s["r"], s["cy"])]
        if t == "polyline":
            return list(s["points"])
        return []

    def get_bbox(self, s):
        t = s["type"]
        if t in ("line", "arrow", "dim"):
            return (min(s["x1"], s["x2"]), min(s["y1"], s["y2"]),
                    abs(s["x2"] - s["x1"]), abs(s["y2"] - s["y1"]))
        if t == "rect":
            return (min(s["x"], s["x"] + s["w"]), min(s["y"], s["y"] + s["h"]),
                    abs(s["w"]), abs(s["h"]))
        if t == "circle":
            return (s["cx"] - s["r"], s["cy"] - s["r"], s["r"] * 2, s["r"] * 2)
        if t in ("polyline", "freehand"):
            xs = [pt[0] for pt in s["points"]]
            ys = [pt[1] for pt in s["points"]]
            return (min(xs), min(ys), max(xs) - min(xs), max(ys) - min(ys))
        if t == "text":
            f = QFont("Arial", pointSize=max(6, int(s["fontSize"])))
            f.setBold(True)
            fm = QFontMetrics(f)
            lines = (s["text"] or "").split("\n")
            max_w = max([20] + [fm.horizontalAdvance(ln) for ln in lines])
            return (s["x"], s["y"], max_w, len(lines) * s["fontSize"] * 1.25)
        return (0, 0, 0, 0)

    def hit_test(self, s, px, py, tol):
        t = s["type"]
        w_half = s.get("width", 1.5) / 2.0
        if t in ("line", "arrow", "dim"):
            return dist_to_segment(px, py, s["x1"], s["y1"], s["x2"], s["y2"]) <= tol + w_half
        if t == "rect":
            x1 = min(s["x"], s["x"] + s["w"])
            x2 = max(s["x"], s["x"] + s["w"])
            y1 = min(s["y"], s["y"] + s["h"])
            y2 = max(s["y"], s["y"] + s["h"])
            if s.get("fill") and x1 <= px <= x2 and y1 <= py <= y2:
                return True
            return min(
                dist_to_segment(px, py, x1, y1, x2, y1),
                dist_to_segment(px, py, x2, y1, x2, y2),
                dist_to_segment(px, py, x2, y2, x1, y2),
                dist_to_segment(px, py, x1, y2, x1, y1),
            ) <= tol + w_half
        if t == "circle":
            d = math.hypot(px - s["cx"], py - s["cy"])
            if s.get("fill") and d <= s["r"] + tol:
                return True
            return abs(d - s["r"]) <= tol + w_half
        if t in ("polyline", "freehand"):
            pts = s["points"]
            for i in range(1, len(pts)):
                if dist_to_segment(px, py, pts[i - 1][0], pts[i - 1][1], pts[i][0], pts[i][1]) <= tol + w_half:
                    return True
            return False
        if t == "text":
            bx, by, bw, bh = self.get_bbox(s)
            return bx - tol <= px <= bx + bw + tol and by - tol <= py <= by + bh + tol
        return False

    def translate_shape(self, s, dx, dy):
        t = s["type"]
        if t in ("line", "arrow", "dim"):
            s["x1"] += dx; s["y1"] += dy; s["x2"] += dx; s["y2"] += dy
        elif t in ("rect", "text"):
            s["x"] += dx; s["y"] += dy
        elif t == "circle":
            s["cx"] += dx; s["cy"] += dy
        elif t in ("polyline", "freehand"):
            s["points"] = [[pt[0] + dx, pt[1] + dy] for pt in s["points"]]

    # === MOUSE & KEYBOARD EVENTS ===
    def mousePressEvent(self, e):
        p = self.active_page()
        if not p:
            return
        sx, sy = e.position().x(), e.position().y()
        tool = self.main_win.current_tool

        if e.button() == Qt.MiddleButton or tool == "pan" or self.space_pressed:
            self.is_panning = True
            self.pan_start = QPointF(sx, sy)
            self.pan_orig = (self.pan_x, self.pan_y)
            self.setCursor(Qt.ClosedHandCursor)
            return

        if e.button() == Qt.RightButton:
            if tool == "polyline" and self.draw_draft:
                self.finish_polyline()
            return

        if e.button() != Qt.LeftButton:
            return

        rx, ry = self.screen_to_pdf(sx, sy)

        if tool == "eraser":
            tol = 7.0 / self.zoom
            for i in range(len(p.shapes) - 1, -1, -1):
                if self.hit_test(p.shapes[i], rx, ry, tol):
                    p.push_undo()
                    p.shapes.pop(i)
                    self.undoStateChanged.emit()
                    self.thumbnailDirty.emit()
                    self.update()
                    break
            return

        if tool == "select":
            tol = 7.0 / self.zoom
            if self.selected_id:
                sel = next((s for s in p.shapes if s["id"] == self.selected_id), None)
                if sel:
                    for hi, (hx, hy) in enumerate(self.get_handles(sel)):
                        if math.hypot(hx - rx, hy - ry) <= 8.0 / self.zoom:
                            self.drag_action = {
                                "mode": "handle", "handle_idx": hi,
                                "start": (rx, ry), "orig": copy.deepcopy(sel), "pushed": False
                            }
                            return
            found = None
            for i in range(len(p.shapes) - 1, -1, -1):
                if self.hit_test(p.shapes[i], rx, ry, tol):
                    found = p.shapes[i]
                    break
            self.selected_id = found["id"] if found else None
            if found:
                self.drag_action = {
                    "mode": "move", "start": (rx, ry),
                    "orig": copy.deepcopy(found), "pushed": False
                }
            self.update()
            return

        if tool == "text":
            sn = self.compute_snapped(rx, ry)
            txt, ok = QInputDialog.getMultiLineText(self, "Chèn văn bản", "Nhập nội dung (hỗ trợ tiếng Việt):")
            if ok and txt.strip():
                p.push_undo()
                s = self.main_win.base_style()
                s.update({"id": str(uuid.uuid4()), "type": "text", "x": sn["x"], "y": sn["y"], "text": txt.strip()})
                p.shapes.append(s)
                self.undoStateChanged.emit()
                self.thumbnailDirty.emit()
                self.update()
            return

        if tool == "freehand":
            s = self.main_win.base_style()
            s.update({"id": str(uuid.uuid4()), "type": "freehand", "points": [[rx, ry]]})
            self.draw_draft = s
            self.update()
            return

        if tool == "polyline":
            anchor = None
            if self.draw_draft and len(self.draw_draft["points"]) >= 2:
                anchor = self.draw_draft["points"][-2]
            sn = self.compute_snapped(rx, ry, anchor)
            if not self.draw_draft:
                s = self.main_win.base_style()
                s.update({"id": str(uuid.uuid4()), "type": "polyline",
                          "points": [[sn["x"], sn["y"]], [sn["x"], sn["y"]]]})
                self.draw_draft = s
            else:
                self.draw_draft["points"][-1] = [sn["x"], sn["y"]]
                self.draw_draft["points"].append([sn["x"], sn["y"]])
            self.update()
            return

        if tool in ("line", "arrow", "dim", "rect", "circle"):
            if not self.draw_draft:
                sn = self.compute_snapped(rx, ry)
                s = self.main_win.base_style()
                s["id"] = str(uuid.uuid4())
                s["type"] = tool
                if tool == "rect":
                    s.update({"x": sn["x"], "y": sn["y"], "w": 0.0, "h": 0.0})
                elif tool == "circle":
                    s.update({"cx": sn["x"], "cy": sn["y"], "r": 0.0})
                else:
                    s.update({"x1": sn["x"], "y1": sn["y"], "x2": sn["x"], "y2": sn["y"],
                              "dimScale": self.main_win.dim_scale})
                self.draw_draft = s
            else:
                self.commit_two_point_draft(rx, ry)
            self.update()

    def commit_two_point_draft(self, rx, ry):
        p = self.active_page()
        if not p or not self.draw_draft:
            return
        d = self.draw_draft
        if d["type"] == "rect":
            sn = self.compute_snapped(rx, ry)
            x1, y1 = d["x"], d["y"]
            d["x"] = min(x1, sn["x"])
            d["y"] = min(y1, sn["y"])
            d["w"] = abs(sn["x"] - x1)
            d["h"] = abs(sn["y"] - y1)
            if d["w"] > 0.5 or d["h"] > 0.5:
                p.push_undo()
                p.shapes.append(d)
                self.undoStateChanged.emit()
                self.thumbnailDirty.emit()
        elif d["type"] == "circle":
            sn = self.compute_snapped(rx, ry)
            d["r"] = math.hypot(sn["x"] - d["cx"], sn["y"] - d["cy"])
            if d["r"] > 0.5:
                p.push_undo()
                p.shapes.append(d)
                self.undoStateChanged.emit()
                self.thumbnailDirty.emit()
        else:
            sn = self.compute_snapped(rx, ry, (d["x1"], d["y1"]))
            d["x2"], d["y2"] = sn["x"], sn["y"]
            if math.hypot(d["x2"] - d["x1"], d["y2"] - d["y1"]) > 0.5:
                if d["type"] == "dim":
                    mm = math.hypot(d["x2"] - d["x1"], d["y2"] - d["y1"]) * PT_TO_MM * self.main_win.dim_scale
                    d["label"] = format_length(mm, True)
                p.push_undo()
                p.shapes.append(d)
                self.undoStateChanged.emit()
                self.thumbnailDirty.emit()
        self.draw_draft = None

    def finish_polyline(self):
        p = self.active_page()
        if p and self.draw_draft and self.draw_draft["type"] == "polyline":
            self.draw_draft["points"].pop()
            if len(self.draw_draft["points"]) >= 2:
                p.push_undo()
                p.shapes.append(self.draw_draft)
                self.undoStateChanged.emit()
                self.thumbnailDirty.emit()
        self.draw_draft = None
        self.update()

    def mouseDoubleClickEvent(self, e):
        if self.main_win.current_tool == "polyline" and self.draw_draft:
            self.finish_polyline()

    def mouseMoveEvent(self, e):
        sx, sy = e.position().x(), e.position().y()
        self.pointer_screen = QPointF(sx, sy)
        self.pointer_inside = True

        if self.is_panning:
            self.pan_x = self.pan_orig[0] + (sx - self.pan_start.x())
            self.pan_y = self.pan_orig[1] + (sy - self.pan_start.y())
            self.update()
            return

        rx, ry = self.screen_to_pdf(sx, sy)
        self.pointer_pdf = QPointF(rx, ry)
        tool = self.main_win.current_tool

        if self.drag_action and tool == "select":
            p = self.active_page()
            sel = next((s for s in p.shapes if s["id"] == self.selected_id), None) if p else None
            if sel:
                if not self.drag_action["pushed"]:
                    p.push_undo()
                    self.undoStateChanged.emit()
                    self.drag_action["pushed"] = True
                orig = self.drag_action["orig"]
                if self.drag_action["mode"] == "move":
                    sel.clear()
                    sel.update(copy.deepcopy(orig))
                    self.translate_shape(sel, rx - self.drag_action["start"][0], ry - self.drag_action["start"][1])
                else:
                    sn = self.compute_snapped(rx, ry)
                    hi = self.drag_action["handle_idx"]
                    if sel["type"] in ("line", "arrow", "dim"):
                        if hi == 0:
                            sel["x1"], sel["y1"] = sn["x"], sn["y"]
                        else:
                            sel["x2"], sel["y2"] = sn["x"], sn["y"]
                        if sel["type"] == "dim":
                            mm = math.hypot(sel["x2"] - sel["x1"], sel["y2"] - sel["y1"]) * PT_TO_MM * sel.get("dimScale", 1)
                            sel["label"] = format_length(mm, True)
                    elif sel["type"] == "rect":
                        if hi == 0:
                            sel["w"] = (orig["x"] + orig["w"]) - sn["x"]
                            sel["h"] = (orig["y"] + orig["h"]) - sn["y"]
                            sel["x"], sel["y"] = sn["x"], sn["y"]
                        else:
                            sel["w"] = sn["x"] - orig["x"]
                            sel["h"] = sn["y"] - orig["y"]
                    elif sel["type"] == "circle":
                        sel["r"] = max(1.0, math.hypot(sn["x"] - sel["cx"], sn["y"] - sel["cy"]))
                    elif sel["type"] == "polyline":
                        sel["points"][hi] = [sn["x"], sn["y"]]
                self.update()
            self.statusChanged.emit()
            return

        if self.draw_draft and self.draw_draft["type"] == "freehand":
            pts = self.draw_draft["points"]
            if math.hypot(rx - pts[-1][0], ry - pts[-1][1]) >= 1.5 / self.zoom:
                pts.append([rx, ry])
            self.update()
            self.statusChanged.emit()
            return

        anchor = None
        if self.draw_draft:
            dt = self.draw_draft["type"]
            if dt in ("line", "arrow", "dim"):
                anchor = (self.draw_draft["x1"], self.draw_draft["y1"])
            elif dt == "polyline" and len(self.draw_draft["points"]) >= 2:
                anchor = self.draw_draft["points"][-2]

        self.snapped = self.compute_snapped(rx, ry, anchor)

        if self.draw_draft:
            dt = self.draw_draft["type"]
            if dt == "rect":
                self.draw_draft["w"] = self.snapped["x"] - self.draw_draft["x"]
                self.draw_draft["h"] = self.snapped["y"] - self.draw_draft["y"]
            elif dt == "circle":
                self.draw_draft["r"] = math.hypot(self.snapped["x"] - self.draw_draft["cx"],
                                                  self.snapped["y"] - self.draw_draft["cy"])
            elif dt == "polyline":
                self.draw_draft["points"][-1] = [self.snapped["x"], self.snapped["y"]]
            else:
                self.draw_draft["x2"] = self.snapped["x"]
                self.draw_draft["y2"] = self.snapped["y"]

        self.update()
        self.statusChanged.emit()

    def mouseReleaseEvent(self, e):
        if self.is_panning:
            self.is_panning = False
            self.refresh_cursor()
        if self.drag_action:
            if self.drag_action["pushed"]:
                p = self.active_page()
                sel = next((s for s in p.shapes if s["id"] == self.selected_id), None) if p else None
                if sel and sel["type"] == "rect":
                    if sel["w"] < 0:
                        sel["x"] += sel["w"]; sel["w"] = abs(sel["w"])
                    if sel["h"] < 0:
                        sel["y"] += sel["h"]; sel["h"] = abs(sel["h"])
                self.thumbnailDirty.emit()
                self.update()
            self.drag_action = None
        if self.draw_draft and self.draw_draft["type"] == "freehand":
            p = self.active_page()
            if p and len(self.draw_draft["points"]) >= 2:
                p.push_undo()
                p.shapes.append(self.draw_draft)
                self.undoStateChanged.emit()
                self.thumbnailDirty.emit()
            self.draw_draft = None
            self.update()

    def leaveEvent(self, e):
        self.pointer_inside = False
        self.update()

    def wheelEvent(self, e):
        if not self.active_page():
            return
        sx, sy = e.position().x(), e.position().y()
        bx, by = self.screen_to_pdf(sx, sy)
        factor = 1.15 if e.angleDelta().y() > 0 else 1.0 / 1.15
        self.zoom = max(0.1, min(12.0, self.zoom * factor))
        self.pan_x = sx - bx * self.zoom
        self.pan_y = sy - by * self.zoom
        self.render_timer.start(160)
        self.update()
        self.statusChanged.emit()

    def refresh_cursor(self):
        t = self.main_win.current_tool
        if self.space_pressed or t == "pan":
            self.setCursor(Qt.OpenHandCursor)
        elif t == "select":
            self.setCursor(Qt.ArrowCursor)
        else:
            self.setCursor(Qt.CrossCursor)

    # === PAINTING ===
    def paintEvent(self, e):
        painter = QPainter(self)
        painter.setRenderHint(QPainter.Antialiasing, True)
        painter.setRenderHint(QPainter.SmoothPixmapTransform, True)

        painter.fillRect(self.rect(), QColor("#0d0f13"))

        p = self.active_page()
        if not p:
            painter.setPen(QColor("#9aa3b2"))
            painter.drawText(self.rect(), Qt.AlignCenter, "Mở file PDF hoặc nhấn 'Tạo mới' để bắt đầu")
            return

        page_rect = QRectF(self.pan_x, self.pan_y, p.width_pt * self.zoom, p.height_pt * self.zoom)

        # Page shadow + white background
        painter.fillRect(page_rect.translated(5, 5), QColor(0, 0, 0, 120))
        painter.fillRect(page_rect, Qt.white)

        if self.bg_pixmap:
            painter.drawPixmap(page_rect, self.bg_pixmap, QRectF(self.bg_pixmap.rect()))

        # World space transform
        painter.save()
        painter.translate(self.pan_x, self.pan_y)
        painter.scale(self.zoom, self.zoom)

        # Page outline
        painter.setPen(QPen(QColor(0, 200, 255, 110), 1.0 / self.zoom))
        painter.setBrush(Qt.NoBrush)
        painter.drawRect(QRectF(0, 0, p.width_pt, p.height_pt))

        # Grid
        if self.main_win.grid_on:
            painter.setPen(QPen(QColor(0, 140, 200, 45), 0.7 / self.zoom))
            gx = 0.0
            while gx <= p.width_pt:
                painter.drawLine(QPointF(gx, 0), QPointF(gx, p.height_pt))
                gx += GRID_STEP_PT
            gy = 0.0
            while gy <= p.height_pt:
                painter.drawLine(QPointF(0, gy), QPointF(p.width_pt, gy))
                gy += GRID_STEP_PT

        for s in p.shapes:
            self.draw_shape(painter, s, s["id"] == self.selected_id)

        if self.draw_draft:
            self.draw_shape(painter, self.draw_draft, False, True)

        painter.restore()

        # Screen-space Crosshair
        if self.main_win.crosshair_on and self.pointer_inside and self.main_win.current_tool != "pan":
            pen = QPen(QColor(0, 200, 255, 90), 1, Qt.DashLine)
            painter.setPen(pen)
            painter.drawLine(QPointF(self.pointer_screen.x(), 0), QPointF(self.pointer_screen.x(), self.height()))
            painter.drawLine(QPointF(0, self.pointer_screen.y()), QPointF(self.width(), self.pointer_screen.y()))

        # OSNAP marker
        if (self.snapped["type"] in ("endpoint", "midpoint") and self.pointer_inside
                and self.main_win.current_tool not in ("pan", "select")):
            sx, sy = self.pdf_to_screen(self.snapped["x"], self.snapped["y"])
            painter.setPen(QPen(QColor("#4ade80"), 2))
            painter.setBrush(Qt.NoBrush)
            if self.snapped["type"] == "endpoint":
                painter.drawRect(QRectF(sx - 5, sy - 5, 10, 10))
            else:
                poly = QPolygonF([QPointF(sx, sy - 6), QPointF(sx + 6, sy + 5), QPointF(sx - 6, sy + 5)])
                painter.drawPolygon(poly)

        # Live CAD HUD tooltip
        if self.draw_draft and self.pointer_inside:
            hud = ""
            d = self.draw_draft
            dt = d["type"]
            if dt in ("line", "arrow", "dim"):
                dx, dy = d["x2"] - d["x1"], d["y2"] - d["y1"]
                mm = math.hypot(dx, dy) * PT_TO_MM * (self.main_win.dim_scale if dt == "dim" else 1.0)
                ang = ((-math.degrees(math.atan2(dy, dx))) + 360.0) % 360.0
                hud = f"L: {format_length(mm, dt == 'dim')}  ∠ {ang:.1f}°"
            elif dt == "circle":
                rmm = d["r"] * PT_TO_MM
                hud = f"R: {rmm:.1f} mm (Ø {rmm * 2:.1f} mm)"
            elif dt == "rect":
                hud = f"{abs(d['w']) * PT_TO_MM:.1f} × {abs(d['h']) * PT_TO_MM:.1f} mm"
            elif dt == "polyline" and len(d["points"]) >= 2:
                a, b = d["points"][-2], d["points"][-1]
                mm = math.hypot(b[0] - a[0], b[1] - a[1]) * PT_TO_MM
                hud = f"Đoạn: {mm:.1f} mm | Chuột phải / Enter: Xong"

            if hud:
                f = QFont("Consolas", 9)
                f.setBold(True)
                painter.setFont(f)
                fm = QFontMetrics(f)
                tw = fm.horizontalAdvance(hud)
                bx = min(self.width() - tw - 20, self.pointer_screen.x() + 14)
                by = max(24, self.pointer_screen.y() - 12)
                box = QRectF(bx, by - 16, tw + 12, 20)
                painter.fillRect(box, QColor(20, 22, 27, 230))
                painter.setPen(QPen(QColor("#00c8ff"), 1))
                painter.drawRect(box)
                painter.drawText(QPointF(bx + 6, by - 2), hud)

    def draw_shape(self, painter: QPainter, s: dict, selected: bool, is_draft: bool = False):
        painter.save()
        col = QColor(s["color"])
        op = s.get("opacity", 1.0)
        col.setAlphaF(op)

        pen = QPen(col, s.get("width", 1.5))
        pen.setCapStyle(Qt.RoundCap)
        pen.setJoinStyle(Qt.RoundJoin)
        if s.get("dashed"):
            pen.setDashPattern([4.0, 3.0])
        painter.setPen(pen)

        if s.get("fill"):
            fcol = QColor(s["color"])
            fcol.setAlphaF(op * 0.25)
            painter.setBrush(QBrush(fcol))
        else:
            painter.setBrush(Qt.NoBrush)

        t = s["type"]
        if t == "line":
            painter.drawLine(QPointF(s["x1"], s["y1"]), QPointF(s["x2"], s["y2"]))
        elif t == "arrow":
            painter.drawLine(QPointF(s["x1"], s["y1"]), QPointF(s["x2"], s["y2"]))
            ang = math.atan2(s["y2"] - s["y1"], s["x2"] - s["x1"])
            hlen = max(8.0, s.get("width", 1.5) * 4.5)
            spread = math.pi / 6.5
            p2 = QPointF(s["x2"], s["y2"])
            w1 = QPointF(s["x2"] - hlen * math.cos(ang - spread), s["y2"] - hlen * math.sin(ang - spread))
            w2 = QPointF(s["x2"] - hlen * math.cos(ang + spread), s["y2"] - hlen * math.sin(ang + spread))
            painter.setBrush(QBrush(col))
            painter.setPen(Qt.NoPen)
            painter.drawPolygon(QPolygonF([p2, w1, w2]))
        elif t == "dim":
            self.draw_dimension(painter, s, col)
        elif t == "rect":
            painter.drawRect(QRectF(s["x"], s["y"], s["w"], s["h"]))
        elif t == "circle":
            r = max(0.2, s["r"])
            painter.drawEllipse(QPointF(s["cx"], s["cy"]), r, r)
        elif t in ("polyline", "freehand"):
            pts = s["points"]
            if len(pts) >= 2:
                poly = QPolygonF([QPointF(pt[0], pt[1]) for pt in pts])
                painter.drawPolyline(poly)
        elif t == "text":
            f = QFont("Arial", pointSize=max(6, int(s["fontSize"])))
            f.setBold(True)
            painter.setFont(f)
            painter.setPen(QPen(col))
            lh = s["fontSize"] * 1.25
            for idx, ln in enumerate((s["text"] or "").split("\n")):
                painter.drawText(QPointF(s["x"], s["y"] + (idx + 0.85) * s["fontSize"] * 1.15), ln)

        if selected and not is_draft:
            bx, by, bw, bh = self.get_bbox(s)
            pad = 4.0 / self.zoom
            sel_pen = QPen(QColor("#00c8ff"), 1.2 / self.zoom, Qt.DashLine)
            painter.setPen(sel_pen)
            painter.setBrush(Qt.NoBrush)
            painter.drawRect(QRectF(bx - pad, by - pad, bw + pad * 2, bh + pad * 2))

            hs = 4.5 / self.zoom
            painter.setPen(QPen(QColor("#0d0f13"), 1.0 / self.zoom))
            painter.setBrush(QBrush(QColor("#00c8ff")))
            for hx, hy in self.get_handles(s):
                painter.drawRect(QRectF(hx - hs, hy - hs, hs * 2, hs * 2))

        painter.restore()

    def draw_dimension(self, painter: QPainter, s: dict, col: QColor):
        x1, y1, x2, y2 = s["x1"], s["y1"], s["x2"], s["y2"]
        dx, dy = x2 - x1, y2 - y1
        length = math.hypot(dx, dy)
        if length < 1.0:
            return
        painter.drawLine(QPointF(x1, y1), QPointF(x2, y2))

        nx, ny = -dy / length, dx / length
        tick = max(6.0, s.get("width", 1.5) * 3.5)
        solid_pen = QPen(col, s.get("width", 1.5))
        painter.setPen(solid_pen)
        painter.drawLine(QPointF(x1 - nx * tick, y1 - ny * tick), QPointF(x1 + nx * tick, y1 + ny * tick))
        painter.drawLine(QPointF(x2 - nx * tick, y2 - ny * tick), QPointF(x2 + nx * tick, y2 + ny * tick))

        label = s.get("label") or format_length(length * PT_TO_MM * s.get("dimScale", 1), True)
        mx, my = (x1 + x2) / 2.0, (y1 + y2) / 2.0
        ang = math.degrees(math.atan2(dy, dx))
        if ang > 90 or ang < -90:
            ang += 180

        painter.save()
        painter.translate(mx, my)
        painter.rotate(ang)
        fsize = max(8, int(s.get("width", 1.5) * 5))
        f = QFont("Arial", pointSize=fsize)
        f.setBold(True)
        painter.setFont(f)
        fm = QFontMetrics(f)
        tw = fm.horizontalAdvance(label)
        th = fm.height()
        painter.fillRect(QRectF(-tw / 2 - 3, -th - 4, tw + 6, th + 2), QColor(255, 255, 255, 215))
        painter.setPen(QPen(col))
        painter.drawText(QPointF(-tw / 2, -5), label)
        painter.restore()


class MainWindow(QMainWindow):
    def __init__(self):
        super().__init__()
        self.setWindowTitle("PDF CAD Studio - Chỉnh sửa & Vẽ kỹ thuật PDF")
        self.resize(1340, 820)

        self.pdf_sources = {}
        self.pages_state = []
        self.active_idx = -1
        self.original_name = "tai-lieu-cad"

        # Tool & CAD properties
        self.current_tool = "line"
        self.color = "#ef4444"
        self.stroke_width = 1.5
        self.dashed = False
        self.fill = False
        self.opacity = 1.0
        self.font_size = 14
        self.dim_scale = 100

        self.ortho_on = False
        self.osnap_on = True
        self.grid_on = False
        self.crosshair_on = True

        self.apply_dark_theme()
        self.build_ui()
        self.setup_shortcuts()

    def apply_dark_theme(self):
        self.setStyleSheet("""
            QMainWindow, QWidget { background: #14161b; color: #e6e9ef; font-family: "Segoe UI", Arial; font-size: 12px; }
            QToolBar { background: #1d2028; border-bottom: 1px solid #323846; spacing: 6px; padding: 4px; }
            QPushButton, QToolButton, QComboBox {
                background: #252934; border: 1px solid #323846; border-radius: 4px; padding: 4px 9px; color: #e6e9ef;
            }
            QPushButton:hover, QToolButton:hover, QComboBox:hover { background: #2f3544; border-color: #4f596e; }
            QToolButton:checked, QPushButton:checked {
                background: rgba(0, 200, 255, 0.2); border-color: #00c8ff; color: #00c8ff; font-weight: bold;
            }
            QListWidget { background: #1d2028; border: 1px solid #323846; outline: none; padding: 4px; }
            QListWidget::item { background: #252934; border: 2px solid #323846; border-radius: 5px; margin: 4px; padding: 4px; }
            QListWidget::item:selected { border-color: #00c8ff; background: rgba(0, 200, 255, 0.12); }
            QStatusBar { background: #1d2028; border-top: 1px solid #323846; color: #9aa3b2; }
        """)

    def build_ui(self):
        # === Top Toolbar (File & Page Actions) ===
        tb_top = QToolBar("Tệp & Trang")
        tb_top.setMovable(False)
        self.addToolBar(Qt.TopToolBarArea, tb_top)

        btn_open = QPushButton("📂 Mở PDF")
        btn_open.setStyleSheet("background:#0284c7; border-color:#0ea5e9; font-weight:bold;")
        btn_open.clicked.connect(self.open_pdf)
        tb_top.addWidget(btn_open)

        btn_new = QPushButton("📄 Tạo mới (A4)")
        btn_new.clicked.connect(self.new_blank_pdf)
        tb_top.addWidget(btn_new)

        btn_merge = QPushButton("➕ Chèn từ PDF")
        btn_merge.clicked.connect(self.merge_pdf)
        tb_top.addWidget(btn_merge)

        btn_blank = QPushButton("📃 + Trang trắng ▾")
        blank_menu = QMenu(btn_blank)
        blank_menu.addAction("Cùng kích thước trang hiện tại", lambda: self.add_blank_page("match"))
        blank_menu.addAction("A4 Dọc (210 × 297 mm)", lambda: self.add_blank_page("a4p"))
        blank_menu.addAction("A4 Ngang (297 × 210 mm)", lambda: self.add_blank_page("a4l"))
        blank_menu.addAction("A3 Ngang (420 × 297 mm)", lambda: self.add_blank_page("a3l"))
        btn_blank.setMenu(blank_menu)
        tb_top.addWidget(btn_blank)

        tb_top.addSeparator()

        self.btn_undo = QPushButton("↶ Hoàn tác")
        self.btn_undo.setEnabled(False)
        self.btn_undo.clicked.connect(self.undo)
        tb_top.addWidget(self.btn_undo)

        self.btn_redo = QPushButton("↷ Làm lại")
        self.btn_redo.setEnabled(False)
        self.btn_redo.clicked.connect(self.redo)
        tb_top.addWidget(self.btn_redo)

        tb_top.addSeparator()
        tb_top.addWidget(QLabel(" Tỉ lệ Dim: "))
        self.cmb_scale = QComboBox()
        for sc in [1, 10, 20, 50, 100, 200, 500]:
            self.cmb_scale.addItem(f"1:{sc}", sc)
        self.cmb_scale.setCurrentIndex(4)
        self.cmb_scale.currentIndexChanged.connect(lambda: setattr(self, "dim_scale", self.cmb_scale.currentData()))
        tb_top.addWidget(self.cmb_scale)

        btn_fit = QPushButton("⛶ Vừa khung")
        btn_fit.clicked.connect(lambda: self.canvas.fit_to_view())
        tb_top.addWidget(btn_fit)

        btn_export = QPushButton("💾 Xuất PDF")
        btn_export.setStyleSheet("background:#15803d; border-color:#22c55e; font-weight:bold;")
        btn_export.clicked.connect(self.export_pdf)
        tb_top.addWidget(btn_export)

        # === Second Toolbar (CAD Styles & Aids) ===
        self.addToolBarBreak(Qt.TopToolBarArea)
        tb_props = QToolBar("Thuộc tính nét & CAD")
        tb_props.setMovable(False)
        self.addToolBar(Qt.TopToolBarArea, tb_props)

        tb_props.addWidget(QLabel(" Màu: "))
        for hex_c in ["#ef4444", "#facc15", "#22c55e", "#00c8ff", "#3b82f6", "#d946ef", "#111827", "#ffffff"]:
            sw = QPushButton()
            sw.setFixedSize(20, 20)
            sw.setStyleSheet(f"background:{hex_c}; border:1px solid #666; border-radius:3px;")
            sw.clicked.connect(lambda _, c=hex_c: self.set_color(c))
            tb_props.addWidget(sw)

        self.btn_custom_col = QPushButton("🎨 Khác")
        self.btn_custom_col.clicked.connect(self.pick_custom_color)
        tb_props.addWidget(self.btn_custom_col)

        tb_props.addWidget(QLabel(" Độ dày: "))
        self.cmb_width = QComboBox()
        for w in [0.75, 1.5, 2.5, 4.0, 7.0, 12.0]:
            self.cmb_width.addItem(f"{w} pt", w)
        self.cmb_width.setCurrentIndex(1)
        self.cmb_width.currentIndexChanged.connect(self.on_style_changed)
        tb_props.addWidget(self.cmb_width)

        self.cmb_dash = QComboBox()
        self.cmb_dash.addItem("─── Nét liền", False)
        self.cmb_dash.addItem("- - - Nét đứt", True)
        self.cmb_dash.currentIndexChanged.connect(self.on_style_changed)
        tb_props.addWidget(self.cmb_dash)

        self.chk_fill = QCheckBox("Tô nền")
        self.chk_fill.stateChanged.connect(self.on_style_changed)
        tb_props.addWidget(self.chk_fill)

        self.chk_hl = QCheckBox("Mờ 40%")
        self.chk_hl.stateChanged.connect(self.on_style_changed)
        tb_props.addWidget(self.chk_hl)

        tb_props.addWidget(QLabel(" Cỡ chữ: "))
        self.cmb_font = QComboBox()
        for fs in [10, 14, 18, 24, 36]:
            self.cmb_font.addItem(f"{fs} pt", fs)
        self.cmb_font.setCurrentIndex(1)
        self.cmb_font.currentIndexChanged.connect(self.on_style_changed)
        tb_props.addWidget(self.cmb_font)

        tb_props.addSeparator()

        self.btn_ortho = QToolButton(text="ORTHO (F8)", checkable=True)
        self.btn_ortho.toggled.connect(lambda v: setattr(self, "ortho_on", v))
        tb_props.addWidget(self.btn_ortho)

        self.btn_osnap = QToolButton(text="OSNAP (F3)", checkable=True, checked=True)
        self.btn_osnap.toggled.connect(lambda v: setattr(self, "osnap_on", v))
        tb_props.addWidget(self.btn_osnap)

        self.btn_grid = QToolButton(text="GRID (F9)", checkable=True)
        self.btn_grid.toggled.connect(lambda v: (setattr(self, "grid_on", v), self.canvas.update()))
        tb_props.addWidget(self.btn_grid)

        self.btn_cross = QToolButton(text="CROSSHAIR", checkable=True, checked=True)
        self.btn_cross.toggled.connect(lambda v: (setattr(self, "crosshair_on", v), self.canvas.update()))
        tb_props.addWidget(self.btn_cross)

        # === Left CAD Toolstrip ===
        tb_left = QToolBar("Công cụ vẽ CAD")
        tb_left.setMovable(False)
        self.addToolBar(Qt.LeftToolBarArea, tb_left)

        self.tool_buttons = {}
        tools = [
            ("select", "Chọn (V)", "Chọn, di chuyển & sửa đỉnh (V)"),
            ("pan", "Kéo (H)", "Kéo vùng nhìn / Chuột giữa (H)"),
            ("line", "Thẳng (L)", "Đoạn thẳng CAD (L)"),
            ("polyline", "Đa tuyến (P)", "Đa tuyến Polyline (P)"),
            ("rect", "Chữ nhật (R)", "Hình chữ nhật (R)"),
            ("circle", "Tròn (C)", "Hình tròn từ tâm + bán kính (C)"),
            ("arrow", "Mũi tên (A)", "Mũi tên chỉ dẫn (A)"),
            ("dim", "Đo Dim (D)", "Đo kích thước theo tỉ lệ (D)"),
            ("freehand", "Bút (F)", "Vẽ tự do / Highlight (F)"),
            ("text", "Chữ (T)", "Chèn chữ tiếng Việt (T)"),
            ("eraser", "Tẩy (E)", "Xóa hình đã vẽ (E)")
        ]
        for key, label, tip in tools:
            b = QToolButton()
            b.setText(label)
            b.setToolTip(tip)
            b.setCheckable(True)
            b.setFixedWidth(78)
            b.clicked.connect(lambda _, k=key: self.set_tool(k))
            tb_left.addWidget(b)
            self.tool_buttons[key] = b
        self.tool_buttons["line"].setChecked(True)

        # === Central Workspace (Pages Sidebar + CAD Canvas) ===
        splitter = QSplitter(Qt.Horizontal)

        sidebar_widget = QWidget()
        sidebar_layout = QVBoxLayout(sidebar_widget)
        sidebar_layout.setContentsMargins(6, 6, 6, 6)
        sidebar_layout.setSpacing(6)

        sidebar_layout.addWidget(QLabel("<b>QUẢN LÝ TRANG</b> (Kéo thả để đổi vị trí)"))
        self.page_list = QListWidget()
        self.page_list.setIconSize(QSize(140, 110))
        self.page_list.setDragDropMode(QAbstractItemView.InternalMove)
        self.page_list.currentRowChanged.connect(self.on_page_selected)
        self.page_list.model().rowsMoved.connect(self.on_pages_reordered)
        sidebar_layout.addWidget(self.page_list)

        # Page Quick Buttons
        pg_btns_1 = QHBoxLayout()
        b_up = QPushButton("▲ Lên"); b_up.clicked.connect(lambda: self.move_page(-1))
        b_dn = QPushButton("▼ Xuống"); b_dn.clicked.connect(lambda: self.move_page(1))
        pg_btns_1.addWidget(b_up); pg_btns_1.addWidget(b_dn)
        sidebar_layout.addLayout(pg_btns_1)

        pg_btns_2 = QHBoxLayout()
        b_rot = QPushButton("↻ Xoay 90°"); b_rot.clicked.connect(self.rotate_current_page)
        b_dup = QPushButton("⧉ Nhân bản"); b_dup.clicked.connect(self.duplicate_current_page)
        b_del = QPushButton("🗑 Xóa"); b_del.setStyleSheet("color:#fca5a5;")
        b_del.clicked.connect(self.delete_current_page)
        pg_btns_2.addWidget(b_rot); pg_btns_2.addWidget(b_dup); pg_btns_2.addWidget(b_del)
        sidebar_layout.addLayout(pg_btns_2)

        sidebar_widget.setMinimumWidth(220)
        sidebar_widget.setMaximumWidth(270)

        self.canvas = CadCanvasWidget(self)
        self.canvas.statusChanged.connect(self.update_status)
        self.canvas.thumbnailDirty.connect(self.refresh_active_thumbnail)
        self.canvas.undoStateChanged.connect(self.update_undo_buttons)

        splitter.addWidget(sidebar_widget)
        splitter.addWidget(self.canvas)
        splitter.setStretchFactor(1, 1)
        self.setCentralWidget(splitter)

        # Status Bar
        self.status_lbl = QLabel("Sẵn sàng")
        self.statusBar().addWidget(self.status_lbl, 1)

    def setup_shortcuts(self):
        QShortcut(QKeySequence("Ctrl+Z"), self, self.undo)
        QShortcut(QKeySequence("Ctrl+Y"), self, self.redo)
        QShortcut(QKeySequence("F3"), self, lambda: self.btn_osnap.toggle())
        QShortcut(QKeySequence("F8"), self, lambda: self.btn_ortho.toggle())
        QShortcut(QKeySequence("F9"), self, lambda: self.btn_grid.toggle())
        QShortcut(QKeySequence("Delete"), self, self.delete_selected_shape)
        QShortcut(QKeySequence("Escape"), self, self.cancel_active_draw)
        QShortcut(QKeySequence("Return"), self, self.finish_active_polyline)

        for k, t in [("V", "select"), ("H", "pan"), ("L", "line"), ("P", "polyline"),
                     ("R", "rect"), ("C", "circle"), ("A", "arrow"), ("D", "dim"),
                     ("F", "freehand"), ("T", "text"), ("E", "eraser")]:
            QShortcut(QKeySequence(k), self, lambda tool=t: self.set_tool(tool))

    def keyPressEvent(self, e):
        if e.key() == Qt.Key_Shift:
            self.canvas.shift_pressed = True
        elif e.key() == Qt.Key_Space and not e.isAutoRepeat():
            self.canvas.space_pressed = True
            self.canvas.refresh_cursor()
        super().keyPressEvent(e)

    def keyReleaseEvent(self, e):
        if e.key() == Qt.Key_Shift:
            self.canvas.shift_pressed = False
        elif e.key() == Qt.Key_Space and not e.isAutoRepeat():
            self.canvas.space_pressed = False
            self.canvas.refresh_cursor()
        super().keyReleaseEvent(e)

    # === DATA & STATE HELPERS ===
    def active_page(self):
        if 0 <= self.active_idx < len(self.pages_state):
            return self.pages_state[self.active_idx]
        return None

    def base_style(self):
        return {
            "color": self.color,
            "width": self.stroke_width,
            "dashed": self.dashed,
            "fill": self.fill,
            "opacity": self.opacity,
            "fontSize": self.font_size
        }

    def set_tool(self, tool):
        if self.canvas.draw_draft and self.canvas.draw_draft["type"] == "polyline":
            self.canvas.finish_polyline()
        self.canvas.draw_draft = None
        if tool != "select":
            self.canvas.selected_id = None
        self.current_tool = tool
        for k, b in self.tool_buttons.items():
            b.setChecked(k == tool)
        self.canvas.refresh_cursor()
        self.canvas.update()
        self.update_status()

    def set_color(self, c):
        self.color = c
        self.apply_style_to_selected()

    def pick_custom_color(self):
        col = QColorDialog.getColor(QColor(self.color), self, "Chọn màu nét vẽ")
        if col.isValid():
            self.set_color(col.name())

    def on_style_changed(self):
        self.stroke_width = self.cmb_width.currentData()
        self.dashed = self.cmb_dash.currentData()
        self.fill = self.chk_fill.isChecked()
        self.opacity = 0.4 if self.chk_hl.isChecked() else 1.0
        self.font_size = self.cmb_font.currentData()
        self.apply_style_to_selected()

    def apply_style_to_selected(self):
        p = self.active_page()
        if not p or not self.canvas.selected_id:
            return
        sel = next((s for s in p.shapes if s["id"] == self.canvas.selected_id), None)
        if sel:
            p.push_undo()
            sel.update(self.base_style())
            self.update_undo_buttons()
            self.canvas.update()
            self.refresh_active_thumbnail()

    def cancel_active_draw(self):
        self.canvas.draw_draft = None
        self.canvas.selected_id = None
        self.canvas.update()

    def finish_active_polyline(self):
        if self.current_tool == "polyline" and self.canvas.draw_draft:
            self.canvas.finish_polyline()

    def delete_selected_shape(self):
        p = self.active_page()
        if p and self.canvas.selected_id:
            p.push_undo()
            p.shapes = [s for s in p.shapes if s["id"] != self.canvas.selected_id]
            self.canvas.selected_id = None
            self.update_undo_buttons()
            self.canvas.update()
            self.refresh_active_thumbnail()

    def undo(self):
        p = self.active_page()
        if p and p.undo_stack:
            p.redo_stack.append(copy.deepcopy(p.shapes))
            p.shapes = p.undo_stack.pop()
            self.canvas.selected_id = None
            self.update_undo_buttons()
            self.canvas.update()
            self.refresh_active_thumbnail()

    def redo(self):
        p = self.active_page()
        if p and p.redo_stack:
            p.undo_stack.append(copy.deepcopy(p.shapes))
            p.shapes = p.redo_stack.pop()
            self.canvas.selected_id = None
            self.update_undo_buttons()
            self.canvas.update()
            self.refresh_active_thumbnail()

    def update_undo_buttons(self):
        p = self.active_page()
        self.btn_undo.setEnabled(bool(p and p.undo_stack))
        self.btn_redo.setEnabled(bool(p and p.redo_stack))

    # === PDF FILE & PAGE OPERATIONS ===
    def open_pdf(self):
        path, _ = QFileDialog.getOpenFileName(self, "Mở file PDF", "", "PDF Files (*.pdf)")
        if not path:
            return
        self.original_name = os.path.splitext(os.path.basename(path))[0]
        self.load_pdf_file(path, insert_after=False)

    def merge_pdf(self):
        path, _ = QFileDialog.getOpenFileName(self, "Chèn trang từ file PDF", "", "PDF Files (*.pdf)")
        if not path:
            return
        self.load_pdf_file(path, insert_after=True)

    def load_pdf_file(self, path, insert_after=False):
        try:
            doc = pymupdf.open(path)
            doc_id = str(uuid.uuid4())
            self.pdf_sources[doc_id] = doc
            new_pages = []
            for idx in range(len(doc)):
                pg = doc[idx]
                new_pages.append(PageState(
                    source_type="pdf", doc_id=doc_id, src_page_index=idx,
                    width_pt=pg.rect.width, height_pt=pg.rect.height, rotation=pg.rotation
                ))
            if not insert_after:
                self.pages_state = new_pages
                self.active_idx = 0 if new_pages else -1
            else:
                ins = self.active_idx + 1 if self.active_idx >= 0 else len(self.pages_state)
                self.pages_state[ins:ins] = new_pages
                self.active_idx = ins
            self.rebuild_page_list(fit=True)
        except Exception as ex:
            QMessageBox.critical(self, "Lỗi mở PDF", str(ex))

    def new_blank_pdf(self):
        self.original_name = "ban-ve-moi"
        self.pages_state = [PageState(source_type="blank", width_pt=595.28, height_pt=841.89)]
        self.active_idx = 0
        self.rebuild_page_list(fit=True)

    def add_blank_page(self, size_key):
        w, h = 595.28, 841.89
        cur = self.active_page()
        if size_key == "match" and cur:
            w, h = cur.width_pt, cur.height_pt
        elif size_key == "a4l":
            w, h = 841.89, 595.28
        elif size_key == "a3l":
            w, h = 1190.55, 841.89
        ins = self.active_idx + 1 if self.active_idx >= 0 else len(self.pages_state)
        self.pages_state.insert(ins, PageState(source_type="blank", width_pt=w, height_pt=h))
        self.active_idx = ins
        self.rebuild_page_list(fit=True)

    def delete_current_page(self):
        if not self.pages_state:
            return
        self.pages_state.pop(self.active_idx)
        if not self.pages_state:
            self.active_idx = -1
        elif self.active_idx >= len(self.pages_state):
            self.active_idx = len(self.pages_state) - 1
        self.rebuild_page_list(fit=False)

    def duplicate_current_page(self):
        p = self.active_page()
        if not p:
            return
        dup = copy.deepcopy(p)
        dup.id = str(uuid.uuid4())
        dup.undo_stack = []
        dup.redo_stack = []
        self.pages_state.insert(self.active_idx + 1, dup)
        self.active_idx += 1
        self.rebuild_page_list(fit=False)

    def move_page(self, delta):
        target = self.active_idx + delta
        if not (0 <= target < len(self.pages_state)):
            return
        p = self.pages_state.pop(self.active_idx)
        self.pages_state.insert(target, p)
        self.active_idx = target
        self.rebuild_page_list(fit=False)

    def rotate_current_page(self):
        p = self.active_page()
        if not p:
            return
        old_w = p.width_pt
        p.width_pt, p.height_pt = p.height_pt, old_w
        p.rotation = (p.rotation + 90) % 360
        for s in p.shapes:
            self.rotate_shape_cw(s, p.width_pt)  # new width == old height
        p.undo_stack.clear()
        p.redo_stack.clear()
        self.rebuild_page_list(fit=True)

    def rotate_shape_cw(self, s, old_h):
        def rp(x, y):
            return (old_h - y, x)
        t = s["type"]
        if t in ("line", "arrow", "dim"):
            s["x1"], s["y1"] = rp(s["x1"], s["y1"])
            s["x2"], s["y2"] = rp(s["x2"], s["y2"])
        elif t == "rect":
            x1, y1 = rp(s["x"], s["y"])
            x2, y2 = rp(s["x"] + s["w"], s["y"] + s["h"])
            s["x"], s["y"] = min(x1, x2), min(y1, y2)
            s["w"], s["h"] = abs(x2 - x1), abs(y2 - y1)
        elif t == "circle":
            s["cx"], s["cy"] = rp(s["cx"], s["cy"])
        elif t in ("polyline", "freehand"):
            s["points"] = [list(rp(pt[0], pt[1])) for pt in s["points"]]
        elif t == "text":
            s["x"], s["y"] = rp(s["x"], s["y"])

    def make_thumbnail_icon(self, p: PageState) -> QIcon:
        tw, th = 140, 105
        scale = min(tw / p.width_pt, th / p.height_pt)
        w, h = max(1, int(p.width_pt * scale)), max(1, int(p.height_pt * scale))
        pm = QPixmap(w, h)
        pm.fill(Qt.white)
        if p.source_type == "pdf":
            src_doc = self.pdf_sources[p.doc_id]
            pg = src_doc[p.src_page_index]
            old_rot = pg.rotation
            if old_rot != p.rotation:
                pg.set_rotation(p.rotation)
            pix = pg.get_pixmap(matrix=pymupdf.Matrix(scale, scale), alpha=False)
            if old_rot != p.rotation:
                pg.set_rotation(old_rot)
            img = QImage(pix.samples, pix.width, pix.height, pix.stride, QImage.Format_RGB888).copy()
            pm = QPixmap.fromImage(img)
        return QIcon(pm)

    def rebuild_page_list(self, fit=False):
        self.page_list.blockSignals(True)
        self.page_list.clear()
        for idx, p in enumerate(self.pages_state):
            item = QListWidgetItem(self.make_thumbnail_icon(p), f"Trang {idx + 1}")
            item.setData(Qt.UserRole, p.id)
            self.page_list.addItem(item)
        if 0 <= self.active_idx < len(self.pages_state):
            self.page_list.setCurrentRow(self.active_idx)
        self.page_list.blockSignals(False)

        self.canvas.selected_id = None
        self.canvas.draw_draft = None
        self.update_undo_buttons()
        if fit:
            self.canvas.fit_to_view()
        else:
            self.canvas.render_pdf_background()
        self.update_status()

    def refresh_active_thumbnail(self):
        p = self.active_page()
        if p and 0 <= self.active_idx < self.page_list.count():
            self.page_list.item(self.active_idx).setIcon(self.make_thumbnail_icon(p))

    def on_page_selected(self, row):
        if 0 <= row < len(self.pages_state) and row != self.active_idx:
            self.active_idx = row
            self.canvas.selected_id = None
            self.canvas.draw_draft = None
            self.update_undo_buttons()
            self.canvas.render_pdf_background()
            self.update_status()

    def on_pages_reordered(self):
        by_id = {p.id: p for p in self.pages_state}
        cur_id = self.pages_state[self.active_idx].id if self.active_page() else None
        new_order = []
        for i in range(self.page_list.count()):
            pid = self.page_list.item(i).data(Qt.UserRole)
            if pid in by_id:
                new_order.append(by_id[pid])
                self.page_list.item(i).setText(f"Trang {i + 1}")
        self.pages_state = new_order
        if cur_id:
            self.active_idx = next((i for i, p in enumerate(self.pages_state) if p.id == cur_id), 0)
        self.update_status()

    def update_status(self):
        p = self.active_page()
        pg_txt = f"Trang: {self.active_idx + 1}/{len(self.pages_state)}" if p else "Trang: -/-"
        zm_txt = f"Zoom: {int(self.canvas.zoom * 100)}%"
        xmm = self.canvas.pointer_pdf.x() * PT_TO_MM
        ymm = self.canvas.pointer_pdf.y() * PT_TO_MM
        self.status_lbl.setText(
            f"{pg_txt}   |   {zm_txt}   |   X: {xmm:.1f} mm, Y: {ymm:.1f} mm   |   Công cụ: {self.current_tool.upper()} (Giữ Shift = Ortho, Chuột giữa = Kéo)"
        )

    # === EXPORT PDF (VECTOR) ===
    def export_pdf(self):
        if not self.pages_state:
            return
        default_name = f"{self.original_name}_edited.pdf"
        out_path, _ = QFileDialog.getSaveFileName(self, "Lưu file PDF", default_name, "PDF Files (*.pdf)")
        if not out_path:
            return

        try:
            out_doc = pymupdf.open()
            font_path = find_vietnamese_font()

            for p in self.pages_state:
                if p.source_type == "blank":
                    out_page = out_doc.new_page(width=p.width_pt, height=p.height_pt)
                else:
                    src_doc = self.pdf_sources[p.doc_id]
                    out_doc.insert_pdf(src_doc, from_page=p.src_page_index, to_page=p.src_page_index)
                    out_page = out_doc[-1]
                    out_page.set_rotation(p.rotation)

                if font_path:
                    out_page.insert_font(fontname="vnfont", fontfile=font_path)
                    fname = "vnfont"
                else:
                    fname = "helv"

                shape = out_page.new_shape()
                for s in p.shapes:
                    col = hex_to_rgb_norm(s["color"])
                    op = s.get("opacity", 1.0)
                    w = s.get("width", 1.5)
                    dashes = f"[{w * 3.5:.1f} {w * 2.5:.1f}] 0" if s.get("dashed") else None
                    fill_col = col if s.get("fill") else None
                    fill_op = op * 0.25 if s.get("fill") else 1.0

                    t = s["type"]
                    if t == "line":
                        shape.draw_line((s["x1"], s["y1"]), (s["x2"], s["y2"]))
                        shape.finish(color=col, width=w, dashes=dashes, stroke_opacity=op, lineCap=1, lineJoin=1)
                    elif t == "arrow":
                        shape.draw_line((s["x1"], s["y1"]), (s["x2"], s["y2"]))
                        shape.finish(color=col, width=w, dashes=dashes, stroke_opacity=op, lineCap=1)
                        ang = math.atan2(s["y2"] - s["y1"], s["x2"] - s["x1"])
                        hlen = max(8.0, w * 4.5)
                        sp = math.pi / 6.5
                        p2 = (s["x2"], s["y2"])
                        w1 = (s["x2"] - hlen * math.cos(ang - sp), s["y2"] - hlen * math.sin(ang - sp))
                        w2 = (s["x2"] - hlen * math.cos(ang + sp), s["y2"] - hlen * math.sin(ang + sp))
                        shape.draw_polyline([p2, w1, w2, p2])
                        shape.finish(color=col, fill=col, width=0.5, stroke_opacity=op, fill_opacity=op)
                    elif t == "dim":
                        dx, dy = s["x2"] - s["x1"], s["y2"] - s["y1"]
                        length = math.hypot(dx, dy)
                        if length >= 1.0:
                            shape.draw_line((s["x1"], s["y1"]), (s["x2"], s["y2"]))
                            shape.finish(color=col, width=w, dashes=dashes, stroke_opacity=op)
                            nx, ny = -dy / length, dx / length
                            tk = max(6.0, w * 3.5)
                            shape.draw_line((s["x1"] - nx * tk, s["y1"] - ny * tk), (s["x1"] + nx * tk, s["y1"] + ny * tk))
                            shape.draw_line((s["x2"] - nx * tk, s["y2"] - ny * tk), (s["x2"] + nx * tk, s["y2"] + ny * tk))
                            shape.finish(color=col, width=w, stroke_opacity=op)
                            lbl = s.get("label") or format_length(length * PT_TO_MM * s.get("dimScale", 1), True)
                            fsize = max(9.0, w * 5.0)
                            mx, my = (s["x1"] + s["x2"]) / 2.0, (s["y1"] + s["y2"]) / 2.0
                            shape.insert_text((mx - len(lbl) * fsize * 0.25, my - 4), lbl,
                                              fontname=fname, fontsize=fsize, color=col, fill_opacity=op)
                    elif t == "rect":
                        rect = pymupdf.Rect(s["x"], s["y"], s["x"] + s["w"], s["y"] + s["h"]).normalize()
                        shape.draw_rect(rect)
                        shape.finish(color=col, fill=fill_col, width=w, dashes=dashes,
                                     stroke_opacity=op, fill_opacity=fill_op, lineJoin=1)
                    elif t == "circle":
                        shape.draw_circle((s["cx"], s["cy"]), max(0.5, s["r"]))
                        shape.finish(color=col, fill=fill_col, width=w, dashes=dashes,
                                     stroke_opacity=op, fill_opacity=fill_op)
                    elif t in ("polyline", "freehand"):
                        if len(s["points"]) >= 2:
                            shape.draw_polyline([tuple(pt) for pt in s["points"]])
                            shape.finish(color=col, width=w, dashes=dashes, stroke_opacity=op, lineCap=1, lineJoin=1)
                    elif t == "text" and s.get("text"):
                        fs = s["fontSize"]
                        for idx, ln in enumerate(s["text"].split("\n")):
                            shape.insert_text((s["x"], s["y"] + (idx + 0.88) * fs * 1.15), ln,
                                              fontname=fname, fontsize=fs, color=col, fill_opacity=op)

                shape.commit()

            out_doc.save(out_path, garbage=3, deflate=True)
            out_doc.close()
            QMessageBox.information(self, "Thành công", f"Đã xuất file PDF thành công tại:\n{out_path}")
        except Exception as ex:
            QMessageBox.critical(self, "Lỗi xuất PDF", str(ex))


if __name__ == "__main__":
    app = QApplication(sys.argv)
    win = MainWindow()
    win.show()
    sys.exit(app.exec())
