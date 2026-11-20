#!/usr/bin/env python3
"""
Where does a third candidate produce a Condorcet cycle?

Fixed: candidates A and B, and three voters arranged with a twist around the
equilateral triangle (each voter near one corner, leaning toward the next).
Every pixel is a possible position for candidate C, coloured by the outcome of
pairwise majority voting. Voters prefer closer candidates.

Sliders
  zoom   size of the candidate triangle relative to the voters.
         1    = candidates as spread out as the voters: the cycle region is a bounded island.
         small = candidates close together compared with the voters: preferences become
                 directional, the walls straighten into lines through A and B (the wedge).
  twist  how far each voter leans from its corner toward the next one (handedness of the cycle).

Coordinates are always shown with A at 0 and B at 1.
Thin lines are the walls: positions of C where some voter majority flips.

Requires numpy and matplotlib.
"""
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import ListedColormap
from matplotlib.patches import Patch
from matplotlib.widgets import Slider

A = np.array([0.0, 0.0])
B = np.array([1.0, 0.0])
C_EQ = np.array([0.5, np.sqrt(3) / 2])          # equilateral position of C
CENTRE = (A + B + C_EQ) / 3

X_RANGE, Y_RANGE, RES = (-2.0, 3.0), (-2.0, 3.0), 500
xs = np.linspace(*X_RANGE, RES)
ys = np.linspace(*Y_RANGE, RES)
GX, GY = np.meshgrid(xs, ys)
PIXEL_AREA = (xs[1] - xs[0]) * (ys[1] - ys[0])

LABELS = ["C wins outright", "C in the middle", "C last", "Condorcet cycle"]
COLOURS = ["#b5d4f4", "#e4e2da", "#f7f6f2", "#d85a30"]


def voters(twist):
    corners = [A, B, C_EQ]
    return [corners[k] + twist * (corners[(k + 1) % 3] - corners[k]) for k in range(3)]


def classify(zoom, twist):
    """Return (category grid, C-beats-A grid, C-beats-B grid, voters in plot coordinates)."""
    V = voters(twist)
    # Real positions: the candidate configuration is scaled by `zoom` about the centre,
    # the voters stay where they are. Plotting is done in candidate units (A=0, B=1).
    real = lambda p: CENTRE + zoom * (p - CENTRE)
    a, b = real(A), real(B)
    cx = CENTRE[0] + zoom * (GX - CENTRE[0])
    cy = CENTRE[1] + zoom * (GY - CENTRE[1])
    dist = lambda v, p: np.hypot(v[0] - p[0], v[1] - p[1])
    dist_c = lambda v: np.hypot(v[0] - cx, v[1] - cy)

    c_over_a = sum((dist_c(v) < dist(v, a)).astype(int) for v in V) >= 2
    c_over_b = sum((dist_c(v) < dist(v, b)).astype(int) for v in V) >= 2
    a_over_b = sum(int(dist(v, a) < dist(v, b)) for v in V) >= 2

    b_over_c = ~c_over_b
    cycle = (a_over_b & b_over_c & c_over_a) | (~a_over_b & ~b_over_c & ~c_over_a)
    wins = c_over_a.astype(int) + c_over_b.astype(int)      # how many of A, B that C beats
    cat = np.where(cycle, 3, 2 - wins)                       # 0 first, 1 middle, 2 last, 3 cycle
    voters_plot = [(v - CENTRE) / zoom + CENTRE for v in V]
    return cat, c_over_a, c_over_b, voters_plot


fig, ax = plt.subplots(figsize=(8, 8.6))
plt.subplots_adjust(bottom=0.2)
cat, ca, cb, vp = classify(1.0, 0.3)
img = ax.imshow(cat, origin="lower", extent=(*X_RANGE, *Y_RANGE),
                cmap=ListedColormap(COLOURS), vmin=-0.5, vmax=3.5, interpolation="nearest")
walls = []
voter_marks = ax.scatter([p[0] for p in vp], [p[1] for p in vp], marker="^", s=70,
                         color="#3c3489", zorder=5, label="voters")
ax.scatter([A[0], B[0]], [A[1], B[1]], s=60, color="black", zorder=6)
ax.annotate("A", A, xytext=(-14, -14), textcoords="offset points")
ax.annotate("B", B, xytext=(6, -14), textcoords="offset points")
ax.scatter([C_EQ[0]], [C_EQ[1]], marker="*", s=140, color="black", zorder=6)
ax.annotate("C (equilateral)", C_EQ, xytext=(8, 6), textcoords="offset points")
ax.set_xlim(*X_RANGE); ax.set_ylim(*Y_RANGE); ax.set_aspect("equal")
handles = [Patch(color=c, label=l) for c, l in zip(COLOURS, LABELS)]
handles.append(plt.Line2D([], [], marker="^", ls="", color="#3c3489", label="voters"))
ax.legend(handles=handles, loc="lower left", fontsize=9, framealpha=0.9)


def draw_walls(c_over_a, c_over_b):
    for w in walls:
        try:
            w.remove()
        except AttributeError:                         # older matplotlib
            for coll in w.collections:
                coll.remove()
    walls.clear()
    for grid in (c_over_a, c_over_b):
        walls.append(ax.contour(GX, GY, grid.astype(float), levels=[0.5],
                                colors="#444441", linewidths=0.7))


def update(_=None):
    zoom, twist = s_zoom.val, s_twist.val
    cat, c_over_a, c_over_b, vp = classify(zoom, twist)
    img.set_data(cat)
    draw_walls(c_over_a, c_over_b)
    voter_marks.set_offsets(np.array(vp))
    cyc = cat == 3
    edge = cyc[0, :].any() or cyc[-1, :].any() or cyc[:, 0].any() or cyc[:, -1].any()
    ax.set_title(f"zoom {zoom:.3f}, twist {twist:.2f}:  cycle area ≈ {cyc.sum() * PIXEL_AREA:.2f}"
                 + ("  (reaches the edge of the view: unbounded at this zoom)" if edge else "  (bounded)"),
                 fontsize=10)
    fig.canvas.draw_idle()


ax_zoom = plt.axes([0.15, 0.09, 0.7, 0.03])
ax_twist = plt.axes([0.15, 0.04, 0.7, 0.03])
s_zoom = Slider(ax_zoom, "zoom", 0.01, 1.5, valinit=1.0)
s_twist = Slider(ax_twist, "twist", 0.05, 0.45, valinit=0.3)
s_zoom.on_changed(update)
s_twist.on_changed(update)
update()

if __name__ == "__main__":
    plt.show()
