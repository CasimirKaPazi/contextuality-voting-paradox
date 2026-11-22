"""Degrees of voters for strategy-proof rules (working note *The Global Form*, Section 7).

Three alternatives a, b, c on an oriented triangle a -> b -> c -> a. A voter's loop takes the voter's
ballot once around the hexagon of rankings, the others fixed. Under strategy-proofness an adjacent swap
that raises y over x can change the outcome only from x to y (for lotteries: move probability from x to
y), so the outcome walks on the triangle and has a winding number, the voter's degree. For a lottery
the degree is the expected winding, (1/3) times the sum over the six steps of the signed probability
moved.

Part 1: one voter, deterministic. All strategy-proof rules (3^6 candidates): degrees 0 or 1, degree 1
        exactly for the dictatorship.
Part 2: two voters, deterministic. All strategy-proof rules, by backtracking: the degree is the same at
        every context, the degrees sum to the winding of the diagonal staircase, and with unanimity
        (identical ballots give their top) only the two dictatorships remain.
Part 3: lotteries, SD-strategy-proof, by linear programming. One voter: the degree ranges over
        [-1/2, 1], the minimum at the random top two. Two and three voters: the degree of a voter is the
        same at every context and the degrees sum to the diagonal staircase winding (largest deviation
        0); with unanimity each degree lies in [0, 1] and they sum to 1; without unanimity a degree can
        be negative.
Part 4: which SD-strategy-proof lotteries are mixtures of deterministic strategy-proof rules (the
        non-contextual models of the scenario in *Gibbard-Satterthwaite as a Scenario*, without
        unanimity)? For one, two and three voters, the polytope of SD-strategy-proof lotteries whose
        degrees are all non-negative has the same support function as the convex hull of the
        deterministic rules in random directions: a model is non-contextual exactly when no degree is
        negative (computed, not proved).
Run: python3 gs_degrees.py   (numpy and scipy; about a minute)
"""
from itertools import permutations, product

import numpy as np
from scipy.optimize import linprog

HEX = [(0, 1, 2), (1, 0, 2), (1, 2, 0), (2, 1, 0), (2, 0, 1), (0, 2, 1)]
POS = {r: k for k, r in enumerate(HEX)}
NAMES = "abc"


def sigma(x, y):
    """Orientation of the move x -> y on the triangle a -> b -> c -> a."""
    return 1 if (y - x) % 3 == 1 else -1


def raised(r, s):
    """Adjacent rankings r -> s: (lowered x, raised y)."""
    k = next(t for t in range(3) if r[t] != s[t])
    return r[k], s[k]


def loop_from(r):
    k = POS[r]
    return [HEX[(k + t) % 6] for t in range(7)]


def prefers(r, x, y):
    return r.index(x) <= r.index(y)


# ---------------------------------------------------------------- deterministic

def walk_winding(outs):
    s = 0
    for x, y in zip(outs, outs[1:]):
        if x != y:
            s += sigma(x, y)
    assert s % 3 == 0
    return s // 3


def sp_pair(R, Rp, x, xp):
    """Voter with true R does not gain by reporting R' and vice versa."""
    return prefers(R, x, xp) and prefers(Rp, xp, x)


def part1():
    found = {}
    for vals in product(range(3), repeat=6):
        f = dict(zip(HEX, vals))
        if all(sp_pair(R, Rp, f[R], f[Rp]) for R in HEX for Rp in HEX):
            d = walk_winding([f[r] for r in loop_from(HEX[0])])
            dictator = all(f[r] == r[0] for r in HEX)
            rng = "".join(sorted(NAMES[v] for v in set(vals)))
            found.setdefault((d, dictator), []).append(rng)
    print("Part 1, one voter, deterministic strategy-proof rules:")
    for (d, dic), rngs in sorted(found.items()):
        print(f"    degree {d}{' (dictatorship)' if dic else ''}: {len(rngs)} rules, ranges {sorted(set(rngs))}")


def sp_rules(n, unanimity=False):
    profs = list(product(HEX, repeat=n))
    idx = {p: i for i, p in enumerate(profs)}
    nbrs = [[] for _ in profs]
    for i, p in enumerate(profs):
        for k in range(n):
            for Rp in HEX:
                if Rp != p[k]:
                    q = p[:k] + (Rp,) + p[k + 1:]
                    nbrs[i].append((idx[q], k))
    dom = [set(range(3)) for _ in profs]
    if unanimity:
        for r in HEX:
            dom[idx[(r,) * n]] = {r[0]}
    order = sorted(range(len(profs)), key=lambda i: len(dom[i]))
    val = [None] * len(profs)
    out = []

    def ok(i, x):
        p = profs[i]
        for j, k in nbrs[i]:
            if val[j] is not None and not sp_pair(p[k], profs[j][k], x, val[j]):
                return False
        return True

    def rec(t):
        if t == len(order):
            out.append(dict(zip(profs, val))); return
        i = order[t]
        for x in sorted(dom[i]):
            if ok(i, x):
                val[i] = x; rec(t + 1); val[i] = None

    rec(0)
    return out


def staircase(f, n, start):
    """All voters at `start`; each step of the hexagon is taken by the voters one after another."""
    prof = [start] * n
    outs = [f[tuple(prof)]]
    for r in loop_from(start)[1:]:
        for k in range(n):
            prof[k] = r
            outs.append(f[tuple(prof)])
    return walk_winding(outs)


def det_degrees(f, n):
    res = []
    for i in range(n):
        vals = set()
        for others in product(HEX, repeat=n - 1):
            outs = [f[others[:i] + (r,) + others[i:]] for r in loop_from(HEX[0])]
            vals.add(walk_winding(outs))
        res.append(vals)
    return res


def part2():
    n = 2
    rules = sp_rules(n)
    bad = 0; tally = {}
    for f in rules:
        ds = det_degrees(f, n)
        if any(len(v) != 1 for v in ds):
            bad += 1; continue
        d = tuple(next(iter(v)) for v in ds)
        bad += {staircase(f, n, s) for s in HEX} != {sum(d)}
        tally[d] = tally.get(d, 0) + 1
    una = sp_rules(n, unanimity=True)
    dicts = sum(all(f[p] == p[k][0] for p in f) for f in una for k in range(n))
    print(f"Part 2, two voters: {len(rules)} deterministic strategy-proof rules; degree not constant or "
          f"not summing to the staircase winding: {bad}; degree vectors {dict(sorted(tally.items()))}; "
          f"with unanimity {len(una)} rules, of which dictatorships: {dicts}")


# ---------------------------------------------------------------- lotteries

def sdsp_system(n, unanimity):
    profs = list(product(HEX, repeat=n))
    idx = {p: i for i, p in enumerate(profs)}
    nv = 3 * len(profs)
    var = lambda i, x: 3 * i + x
    A_ub, b_ub, A_eq, b_eq = [], [], [], []
    for i, p in enumerate(profs):
        row = np.zeros(nv); row[[var(i, x) for x in range(3)]] = 1
        A_eq.append(row); b_eq.append(1.0)
        for k in range(n):
            R = p[k]
            for Rp in HEX:
                if Rp == R:
                    continue
                j = idx[p[:k] + (Rp,) + p[k + 1:]]
                for top in (1, 2):  # upper contour sets of the true ranking
                    row = np.zeros(nv)
                    for x in R[:top]:
                        row[var(j, x)] += 1; row[var(i, x)] -= 1
                    A_ub.append(row); b_ub.append(0.0)  # p_j(U) <= p_i(U)
    if unanimity:
        for r in HEX:
            i = idx[(r,) * n]
            row = np.zeros(nv); row[var(i, r[0])] = 1
            A_eq.append(row); b_eq.append(1.0)
    return profs, idx, nv, var, (np.array(A_ub), np.array(b_ub), np.array(A_eq), np.array(b_eq))


def step_flow(nv, var, i, j, x, y):
    """Expected signed displacement of the move from profile i to j that raises y over x."""
    row = np.zeros(nv)
    row[var(i, x)] += sigma(x, y); row[var(j, x)] -= sigma(x, y)
    return row


def degree_row(nv, var, idx, n, k, prof):
    row = np.zeros(nv)
    seq = [prof[:k] + (r,) + prof[k + 1:] for r in loop_from(prof[k])]
    for p, q in zip(seq, seq[1:]):
        x, y = raised(p[k], q[k])
        row += step_flow(nv, var, idx[p], idx[q], x, y)
    return row / 3


def staircase_row(nv, var, idx, n, start):
    row = np.zeros(nv)
    prof = [start] * n
    for r in loop_from(start)[1:]:
        for k in range(n):
            p = tuple(prof); prof[k] = r; q = tuple(prof)
            x, y = raised(p[k], q[k])
            row += step_flow(nv, var, idx[p], idx[q], x, y)
    return row / 3


def extremes(c, system):
    A_ub, b_ub, A_eq, b_eq = system
    lo = linprog(c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=(0, 1), method="highs")
    hi = linprog(-c, A_ub=A_ub, b_ub=b_ub, A_eq=A_eq, b_eq=b_eq, bounds=(0, 1), method="highs")
    return lo.fun, -hi.fun, lo.x


def part3():
    profs, idx, nv, var, sysm = sdsp_system(1, False)
    lo, hi, x = extremes(degree_row(nv, var, idx, 1, 0, (HEX[0],)), sysm)
    top_two = all(abs(x[var(idx[(r,)], r[0])] - .5) < 1e-9 and abs(x[var(idx[(r,)], r[1])] - .5) < 1e-9
                  for r in HEX)
    print(f"Part 3, one voter, SD-strategy-proof lotteries: degree ranges over [{lo:.4f}, {hi:.4f}]; "
          f"the minimiser is the random top two: {top_two}")
    for n in (2, 3):
        for una in (False, True):
            profs, idx, nv, var, sysm = sdsp_system(n, una)
            base = tuple([HEX[0]] * n)
            dev = 0.0
            d0 = degree_row(nv, var, idx, n, 0, base)
            contexts = [p for p in profs if p[0] == HEX[0]][1:]
            for p in contexts:
                lo, hi, _ = extremes(degree_row(nv, var, idx, n, 0, p) - d0, sysm)
                dev = max(dev, abs(lo), abs(hi))
            tot = sum(degree_row(nv, var, idx, n, k, base) for k in range(n))
            lo, hi, _ = extremes(tot - staircase_row(nv, var, idx, n, HEX[0]), sysm)
            dev = max(dev, abs(lo), abs(hi))
            dlo, dhi, _ = extremes(d0, sysm)
            slo, shi, _ = extremes(staircase_row(nv, var, idx, n, HEX[0]), sysm)
            print(f"Part 3, {n} voters, {'with' if una else 'without'} unanimity: largest change of a voter's "
                  f"degree between contexts or of (sum of degrees - staircase winding): {dev:.1e}; "
                  f"degree of voter 0 in [{dlo:.4f}, {dhi:.4f}]; staircase winding in [{slo:.4f}, {shi:.4f}]")


def part4(directions={1: 1000, 2: 500, 3: 150}, seed=2):
    rng = np.random.default_rng(seed)
    for n, trials in directions.items():
        rules = sp_rules(n)
        profs, idx, nv, var, (A_ub, b_ub, A_eq, b_eq) = sdsp_system(n, False)
        V = np.zeros((len(rules), nv))
        for r, f in enumerate(rules):
            for p, x in f.items():
                V[r, var(idx[p], x)] = 1
        degs = [degree_row(nv, var, idx, n, k, tuple([HEX[0]] * n)) for k in range(n)]
        A2 = np.vstack([A_ub] + [-d for d in degs]); b2 = np.concatenate([b_ub, np.zeros(n)])
        gap = 0.0
        for _ in range(trials):
            c = rng.normal(size=nv)
            res = linprog(-c, A_ub=A2, b_ub=b2, A_eq=A_eq, b_eq=b_eq, bounds=(0, 1), method="highs")
            gap = max(gap, -res.fun - (V @ c).max())
        print(f"Part 4, {n} voter(s): {len(rules)} deterministic strategy-proof rules; largest gap between "
              f"the support functions of (SD-strategy-proof, all degrees >= 0) and their convex hull over "
              f"{trials} random directions: {gap:.1e}")


if __name__ == "__main__":
    part1(); part2(); part3(); part4()
