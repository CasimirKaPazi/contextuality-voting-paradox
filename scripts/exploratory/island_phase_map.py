#!/usr/bin/env python3
"""
Phase map: size of the Condorcet-cycle region as a function of zoom and twist.

For each (zoom, twist), the third candidate C is swept over a window in candidate units
(A at 0, B at 1); the area of positions giving a cycle is measured. Sign = direction of the
cycle (+ for A>B>C>A, - for the reverse). Cells where the cycle region reaches the window
edge (unbounded at that zoom) are outlined: there the area is truncated by the window.

Same model as condorcet_island.py: three voters, each near one corner of the equilateral
triangle, shifted a fraction `twist` toward the next corner; voters prefer closer candidates.
Requires numpy and matplotlib.
"""
import numpy as np
import matplotlib.pyplot as plt
from matplotlib.colors import TwoSlopeNorm

A = np.array([0.0, 0.0]); B = np.array([1.0, 0.0]); C_EQ = np.array([0.5, np.sqrt(3) / 2])
CENTRE = (A + B + C_EQ) / 3
WIN, RES = (-4.0, 5.0), 260
xs = np.linspace(*WIN, RES); GX, GY = np.meshgrid(xs, xs)
PIX = (xs[1] - xs[0]) ** 2

def signed_area(zoom, twist):
    corners = [A, B, C_EQ]
    V = [corners[k] + twist * (corners[(k + 1) % 3] - corners[k]) for k in range(3)]
    real = lambda p: CENTRE + zoom * (p - CENTRE)
    a, b = real(A), real(B)
    cx = CENTRE[0] + zoom * (GX - CENTRE[0]); cy = CENTRE[1] + zoom * (GY - CENTRE[1])
    d = lambda v, p: np.hypot(v[0] - p[0], v[1] - p[1])
    dc = lambda v: np.hypot(v[0] - cx, v[1] - cy)
    c_a = sum((dc(v) < d(v, a)).astype(int) for v in V) >= 2
    c_b = sum((dc(v) < d(v, b)).astype(int) for v in V) >= 2
    a_b = sum(int(d(v, a) < d(v, b)) for v in V) >= 2
    fwd = a_b & ~c_b & c_a                    # A>B, B>C, C>A
    rev = ~a_b & c_b & ~c_a                   # B>A, C>B, A>C
    cyc = fwd | rev
    edge = cyc[0].any() or cyc[-1].any() or cyc[:, 0].any() or cyc[:, -1].any()
    return (fwd.sum() - rev.sum()) * PIX, edge

zooms = np.geomspace(0.01, 1.5, 60)
twists = np.linspace(0.01, 0.99, 61)
area = np.zeros((len(twists), len(zooms))); edge = np.zeros_like(area, dtype=bool)
for i, t in enumerate(twists):
    for j, z in enumerate(zooms):
        area[i, j], edge[i, j] = signed_area(z, t)

if __name__ == "__main__":
    fig, ax = plt.subplots(figsize=(8, 6))
    lim = np.abs(area).max()
    m = ax.pcolormesh(zooms, twists, area, cmap="RdBu_r", norm=TwoSlopeNorm(0, -lim, lim), shading="nearest")
    ax.contour(zooms, twists, edge.astype(float), levels=[0.5], colors="black", linewidths=1)
    ax.set_xscale("log"); ax.set_xlabel("zoom (candidate spread / voter spread)"); ax.set_ylabel("twist")
    ax.set_title("Signed area of the cycle region (black line: beyond it, region reaches window edge)", fontsize=10)
    fig.colorbar(m, label="signed cycle area (candidate units²)")
    plt.tight_layout(); plt.show()
