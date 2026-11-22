"""Who can agree under CORE when participants' losses differ in curvature (outcomes on a line).

Each participant j has loss h_j(|x - p_j|) with h_j(d) = d**g_j: strictly concave (g < 1), linear
(g = 1) or convex (g > 1); peaks are available outcomes, plus a grid of further points.
Part 1: groups of concave or linear members: the random ballot can be improved (some member
        strictly better, all weakly) exactly when both extreme members are linear and some peak lies
        between them; checked against linear programming.
Part 2: the construction for that case (mass from the extreme peaks to their inner neighbours,
        keeping the mean) and the three-member weights for the other case.
Part 3: share of random groups, by composition, whose random ballot can be improved.
Part 4: which participants rational groups can push below their endowment (the linear program
        of rational_floor.py), by the participant's curvature and whether some other participant
        has convex loss.
Run: python3 curvature.py   (needs numpy, scipy; part 4 imports rational_floor.py)
"""
import itertools
from collections import defaultdict
import numpy as np
from scipy.optimize import linprog
from rational_floor import rational_floor, floors

rng = np.random.default_rng(21)

def losses(pos, g, out):
    return np.abs(pos[:, None] - out[None, :]) ** np.asarray(g)[:, None]

def improvable(U):
    n, K = U.shape; ideal = U.argmax(1); E = np.zeros(K)
    for j in range(n): E[ideal[j]] += 1 / n
    res = linprog(-U.sum(0), A_ub=-U, b_ub=-(U @ E), A_eq=np.ones((1, K)), b_eq=[1], bounds=(0, 1), method="highs")
    return -res.fun - U.sum(0) @ E > 1e-8

def exponent(kind):
    return {"concave": rng.uniform(0.2, 0.95), "linear": 1.0, "convex": rng.uniform(1.3, 3.0)}[kind]

def part1(T=4000):
    wrong = 0
    for _ in range(T):
        n = int(rng.integers(2, 8)); lin = rng.random(n) < 0.5
        g = np.where(lin, 1.0, rng.uniform(0.2, 0.95, n))
        pos = rng.uniform(0, 1, n); out = np.concatenate([pos, np.linspace(-0.1, 1.1, 30)])
        o = np.argsort(pos); pred = n >= 3 and lin[o[0]] and lin[o[-1]]
        wrong += improvable(-losses(pos, g, out)) != pred
    print(f"Part 1: groups of 2 to 7 concave or linear members; the criterion disagrees with the LP in {wrong} of {T}")

def part2(T=3000):
    worst_ext, worst_int = 0.0, np.inf
    for _ in range(T):          # construction: extremes linear, interior arbitrary increasing losses
        s = int(rng.integers(3, 8)); q = np.sort(rng.uniform(0, 1, s))
        g = np.ones(s); g[1:-1] = rng.uniform(0.2, 3.0, s - 2)
        eps = 1e-3 / s; a = eps; b = a * (q[1] - q[0]) / (q[-1] - q[-2])
        p = np.full(s, 1 / s); p2 = p.copy(); p2[0] -= a; p2[1] += a; p2[-1] -= b; p2[-2] += b
        L = losses(q, g, q)
        d = L @ p2 - L @ p
        worst_ext = max(worst_ext, abs(d[0]), abs(d[-1])); worst_int = min(worst_int, (-d[1:-1]).min())
    print(f"Part 2: construction: largest change for the linear extremes {worst_ext:.1e}; "
          f"smallest gain of an interior member {worst_int:.1e} (positive)")
    bad = 0
    for _ in range(T):          # three members: weights equalising the weighted loss at the peaks
        q = np.sort(rng.uniform(0, 1, 3)); kinds = rng.choice(["concave", "linear"], 3)
        if kinds[0] == "linear" and kinds[2] == "linear": kinds[rng.integers(0, 3, 1)[0] % 2 * 2] = "concave"
        g = np.array([exponent(k) for k in kinds]); C = losses(q, g, q)      # C[j, k]: loss of j at peak k
        lam = np.linalg.solve(C.T, np.ones(3))
        t, D = q[1] - q[0], q[2] - q[0]
        crit = (t / D) ** g[0] + ((D - t) / D) ** g[2] > 1
        bad += (lam.min() > 0) != crit or not crit
    print(f"Part 2: three members, an extreme strictly concave: weights positive and criterion > 1 fails in {bad} of {T}")

def part3(T=2500):
    tab = defaultdict(list)
    for _ in range(T):
        n = int(rng.integers(2, 5)); kind = sorted(rng.choice(["concave", "linear", "convex"], n))
        g = [exponent(k) for k in kind]; pos = rng.uniform(0, 1, n)
        out = np.concatenate([pos, np.linspace(-0.1, 1.1, 25)])
        tab[tuple(kind)].append(improvable(-losses(pos, g, out)))
    print("Part 3: share of groups whose random ballot can be improved, by composition (number of groups)")
    for k in sorted(tab, key=lambda k: (len(k), k)):
        print(f"  {' + '.join(k):36s} {np.mean(tab[k]):.2f} ({len(tab[k])})")

def part4(T=500):
    tab = defaultdict(lambda: [0, 0, 0.0])
    for _ in range(T):
        n = int(rng.integers(3, 6)); kind = rng.choice(["concave", "linear", "convex"], n)
        g = [exponent(k) for k in kind]; pos = rng.uniform(0, 1, n)
        U = -losses(pos, g, np.concatenate([pos, np.linspace(-0.1, 1.1, 12)]))
        for i in range(n):
            f, e = floors(U, i); G, _ = rational_floor(U, i)
            other = "some other convex" if any(kind[j] == "convex" for j in range(n) if j != i) else "no other convex"
            r = tab[(kind[i], other)]; r[0] += 1; r[1] += G < e - 1e-9; r[2] = max(r[2], (e - G) / (U[i].max() - U[i].min()))
    print("Part 4: pushed below the endowment by rational groups (cases, share, largest shortfall in units of range)")
    for k in sorted(tab): print(f"  {k[0]:8s} {k[1]:18s} {tab[k][0]:4d}  {tab[k][1] / tab[k][0]:.2f}  {tab[k][2]:.3f}")

if __name__ == "__main__":
    part1(); part2(); part3(); part4()
