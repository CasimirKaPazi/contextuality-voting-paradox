"""Tie-breakers for maximal lotteries: what proportionality and independence of clones determine.

Checks Section 8 of notes/equality-of-voters-and-alternatives.md.
  1. Full ties (all margins zero), Proposition 14. A neutral rule that is proportional there gives the
     candidate in position k of a ballot the weight w_k. The script solves the linear equations that
     independence of clones puts on the weights for m and m + 1 candidates (m = 2, 3, 4) and checks
     that every solution is a T + (1 - a) B on fully tied profiles with three or more candidates,
     T the shares of first places and B the shares of last places; that T = B for three candidates
     and not for four; and that some fully tied profile of four candidates has a candidate with no
     first place and some last places.
  2. Away from full ties two tie-breakers are compared, both a random voter choosing a maximal
     lottery: the one that gives the most to the voter's first candidate, then to the second, and so
     on (Proposition 6), and the one that gives the least to the voter's last candidate, then to the
     second last, and so on. Both are independent of clones on random profiles; they differ at the
     20-voter tie between two cycles.
Run: python3 equality_tie_breakers.py   (needs numpy and scipy; about half a minute)
"""
import itertools
import numpy as np
from scipy.optimize import linprog

rng = np.random.default_rng(0)


def null_space(A, tol=1e-10):
    _, s, vt = np.linalg.svd(A)
    return vt[(s > tol).sum():].T


def margin_map(rankings, m):
    """Rows: pairs of candidates; columns: rankings; entry +1 if the first of the pair is above."""
    pairs = list(itertools.combinations(range(m), 2))
    A = np.zeros((len(pairs), len(rankings)))
    for j, r in enumerate(rankings):
        for i, (u, v) in enumerate(pairs):
            A[i, j] = 1 if r.index(u) < r.index(v) else -1
    return A


def firsts_and_lasts(shares, rankings, m):
    T, B = np.zeros(m), np.zeros(m)
    for s, r in zip(shares, rankings):
        T[r[0]] += s
        B[r[-1]] += s
    return T, B


def tied_profiles(rankings, m, count):
    """Random share vectors with all margins zero."""
    Z = null_space(margin_map(rankings, m))
    out = []
    while len(out) < count:
        s = np.ones(len(rankings)) / len(rankings) + Z @ rng.normal(size=Z.shape[1]) * 0.3 / len(rankings)
        if (s > 0).all():
            out.append(s / s.sum())
    return out


# ---------- 1. full ties ----------
for m in (2, 3, 4):
    R, R1 = list(itertools.permutations(range(m))), list(itertools.permutations(range(m + 1)))
    adjacent = [r for r in R1 if abs(r.index(0) - r.index(m)) == 1]      # the clones are 0 and m
    D = null_space(margin_map(adjacent, m + 1))                        # fully tied, clones adjacent
    rows = []
    for d in D.T:                                                      # unknowns: w (m), w' (m + 1)
        for y in range(m):
            row = np.zeros(2 * m + 1)
            for coefficient, r in zip(d, adjacent):
                merged = tuple(x for x in r if x != m)
                row[merged.index(y)] -= coefficient
                row[m + r.index(y)] += coefficient
                if y == 0:
                    row[m + r.index(m)] += coefficient
            rows.append(row)
    rows += [np.r_[np.ones(m), np.zeros(m + 1)], np.r_[np.zeros(m), np.ones(m + 1)]]
    A, rhs = np.array(rows), np.r_[np.zeros(len(rows) - 2), 1, 1]
    particular = np.linalg.lstsq(A, rhs, rcond=None)[0]
    assert np.allclose(A @ particular, rhs, atol=1e-9)
    N = null_space(A)
    report = []
    for size, rankings, part in [(m, R, slice(0, m)), (m + 1, R1, slice(m, 2 * m + 1))]:
        profiles = tied_profiles(rankings, size, 8)
        gap = max(np.abs(np.subtract(*firsts_and_lasts(s, rankings, size))).max() for s in profiles)
        for _ in range(6):
            w = (particular + N @ rng.normal(size=N.shape[1]))[part]
            X, Y = [], []
            for s in profiles:
                T, B = firsts_and_lasts(s, rankings, size)
                L = np.zeros(size)
                for share, r in zip(s, rankings):
                    for k, x in enumerate(r):
                        L[x] += share * w[k]
                X += [[T[y], B[y], 1 / size] for y in range(size)]
                Y += list(L)
            X, Y = np.array(X), np.array(Y)
            a, b, c = np.linalg.lstsq(X, Y, rcond=None)[0]
            assert np.allclose(X @ np.array([a, b, c]), Y, atol=1e-9)
            if size >= 3 and gap > 1e-6:
                assert abs(c) < 1e-9 and abs(a + b - 1) < 1e-9
            if size == 3:
                assert gap < 1e-12                                      # T = B: the lottery is T
                assert np.allclose(Y, np.array(X)[:, 0], atol=1e-9)
        report.append(f"{size} candidates: largest |T - B| {gap:.3f}")
    print(f"1. clones from {m} to {m + 1} candidates: {N.shape[1]} free parameters in the weights;"
          f" every solution is a T + (1 - a) B on full ties with three or more candidates ({'; '.join(report)})")
R4 = list(itertools.permutations(range(4)))
cost = np.array([-(r[-1] == 0) for r in R4], dtype=float)               # most last places for candidate 0
A_eq = np.vstack([margin_map(R4, 4), np.ones(len(R4)), [float(r[0] == 0) for r in R4]])
res = linprog(cost, A_eq=A_eq, b_eq=np.r_[np.zeros(6), 1, 0], bounds=(0, 1), method="highs")
print(f"   four candidates, a full tie in which one candidate is never first and is last on a share"
      f" {-res.fun:.3f} of the ballots: " + ", ".join(f"{s:.3f} {''.join('abcd'[x] for x in r)}"
                                                        for s, r in zip(res.x, R4) if s > 1e-9))
assert -res.fun > 0.1

# ---------- 2. two tie-breakers away from full ties ----------
def margins(profile, m):
    G = np.zeros((m, m))
    for r in profile:
        for i, x in enumerate(r):
            for y in r[i + 1:]:
                G[x, y] += 1
                G[y, x] -= 1
    return G


def choose(G, ballot, mode):
    """The voter's maximal lottery: best first (largest for the first candidate, then the second ...)
    or worst last (smallest for the last candidate, then the second last ...)."""
    m = len(G)
    A_eq, b_eq = [np.ones(m)], [1.0]
    sequence, sign = (ballot[:-1], -1) if mode == "best first" else (tuple(reversed(ballot[1:])), 1)
    for x in sequence:
        e = np.zeros(m)
        e[x] = 1
        res = linprog(sign * e, A_ub=-G.T, b_ub=np.zeros(m), A_eq=np.array(A_eq), b_eq=b_eq,
                      bounds=(0, 1), method="highs")
        A_eq.append(e)
        b_eq.append(res.x[x])
    return res.x


def rule(profile, m, mode):
    G = margins(profile, m)
    return sum(profile.count(r) / len(profile) * choose(G, r, mode) for r in set(profile))


def clone(profile, x, m, extra):
    out = []
    for r in profile:
        i, group = r.index(x), [x] + list(range(m, m + extra))
        rng.shuffle(group)
        out.append(r[:i] + tuple(int(g) for g in group) + r[i + 1:])
    return out


def merged(L, x, m):
    out = L[:m].copy()
    out[x] += L[m:].sum()
    return out


cases = 0
for m, extra, trials in [(3, 1, 300), (3, 2, 100), (4, 1, 100)]:
    ranks = list(itertools.permutations(range(m)))
    for _ in range(trials):
        prof = [ranks[i] for i in rng.integers(len(ranks), size=int(rng.choice([2, 4, 6])))]
        x = int(rng.integers(m))
        cloned = clone(prof, x, m, extra)
        for mode in ("best first", "worst last"):
            assert np.allclose(merged(rule(cloned, m + extra, mode), x, m), rule(prof, m, mode), atol=1e-7)
        if not margins(prof, m).any():                                  # full tie: both are random ballot
            T = np.array([sum(r[0] == y for r in prof) for y in range(m)]) / len(prof)
            assert np.allclose(rule(prof, m, "best first"), T) and np.allclose(rule(prof, m, "worst last"), T)
        cases += 1
print(f"2. best first and worst last: both independent of clones on {cases} random profiles")

tie = []                                                                # the 20-voter tie between two cycles
for (x, y), v in zip(itertools.combinations(range(4), 2), [-4, -4, 2, -4, -2, -4]):
    x, y = (x, y) if v > 0 else (y, x)
    rest = [z for z in range(4) if z not in (x, y)]
    tie += [(x, y, *rest), (*reversed(rest), x, y)] * (abs(v) // 2)
G = margins(tie, 4)
both = {mode: rule(tie, 4, mode) for mode in ("best first", "worst last")}
print(f"   at the 20-voter tie between two cycles: best first {both['best first'].round(4)},"
      f" worst last {both['worst last'].round(4)}")
print(f"   the voter a > d > b > c: best first {np.abs(choose(G, (0, 3, 1, 2), 'best first')).round(3)},"
      f" worst last {np.abs(choose(G, (0, 3, 1, 2), 'worst last')).round(3)}")
assert not np.allclose(both["best first"], both["worst last"], atol=1e-3)
for x in range(4):
    for extra in (1, 2):
        cloned = clone(tie, x, 4, extra)
        for mode in both:
            assert np.allclose(merged(rule(cloned, 4 + extra, mode), x, 4), both[mode], atol=1e-7)
print("   both independent of clones at this profile, with any candidate replaced by two or three clones")
print("all checks passed")
