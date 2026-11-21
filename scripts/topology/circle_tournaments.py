"""Which tournaments can be placed on the circle?

Value space of *Cycles and Twists*, Section 2: points on R/Z, with u placed
above v iff u is less than half a turn ahead of v.  A tournament is realised
if every x beating y in T gets a point less than half a turn ahead of y's.

Check: every locally transitive (= round, Brouwer 1980) tournament is
realisable, and no other.  The "no other" direction is a two-line proof
(an open half circle carries a linear order); this script checks the
other direction exhaustively for small n.

Round tournaments with cyclic order 0, 1, ..., n-1: vertex i beats exactly
the d_i vertices immediately behind it, i-1, ..., i-d_i (mod n).  For a
fixed degree sequence realisability is a linear program in the gaps
between consecutive points; we maximise a common slack eps.
"""
import itertools
import numpy as np
from scipy.optimize import linprog


def is_tournament(d, n):
    for i in range(n):
        for k in range(1, n):
            j = (i - k) % n          # j is k steps behind i
            i_beats_j = d[i] >= k
            j_beats_i = d[j] >= n - k  # i is n-k steps behind j
            if i_beats_j == j_beats_i:
                return False
    return True


def realisable(d, n):
    # variables: gaps g_0..g_{n-1} (g_m = x_m - x_{m-1} mod 1), eps
    # D(i, k) = g_i + g_{i-1} + ... + g_{i-k+1}  (distance from i back to i-k)
    nv = n + 1
    A, b = [], []

    def dist_row(i, k):
        r = np.zeros(nv)
        for t in range(k):
            r[(i - t) % n] = 1
        return r

    for i in range(n):
        if d[i] >= 1:                     # D(i, d_i) <= 1/2 - eps
            r = dist_row(i, d[i]); r[n] = 1
            A.append(r); b.append(0.5)
        if d[i] + 1 <= n - 1:             # D(i, d_i + 1) >= 1/2 + eps
            r = -dist_row(i, d[i] + 1); r[n] = 1
            A.append(r); b.append(-0.5)
    for m in range(n):                    # g_m >= eps
        r = np.zeros(nv); r[m] = -1; r[n] = 1
        A.append(r); b.append(0.0)
    Aeq = [np.r_[np.ones(n), 0.0]]; beq = [1.0]
    c = np.zeros(nv); c[n] = -1
    res = linprog(c, A_ub=A, b_ub=b, A_eq=Aeq, b_eq=beq,
                  bounds=[(0, 1)] * n + [(None, 1)], method="highs")
    return res.status == 0 and -res.fun > 1e-9


def canonical(d, n):
    """Tournament as adjacency, canonical up to relabelling (brute force)."""
    beats = {(i, (i - k) % n) for i in range(n) for k in range(1, d[i] + 1)}
    best = None
    for p in itertools.permutations(range(n)):
        key = tuple(sorted((p[a], p[b]) for a, b in beats))
        if best is None or key < best:
            best = key
    return best


def locally_transitive(beats, n):
    out = {v: {w for (u, w) in beats if u == v} for v in range(n)}
    inn = {v: {u for (u, w) in beats if w == v} for v in range(n)}

    def transitive(S):
        return all(not ((a, b) in beats and (b, c) in beats and (c, a) in beats)
                   for a in S for b in S for c in S)
    return all(transitive(out[v]) and transitive(inn[v]) for v in range(n))


if __name__ == "__main__":
    for n in range(3, 9):
        total = feasible = 0
        failures = []
        for d in itertools.product(range(n), repeat=n):
            if sum(d) != n * (n - 1) // 2 or not is_tournament(d, n):
                continue
            total += 1
            if realisable(d, n):
                feasible += 1
            else:
                failures.append(d)
        print(f"n={n}: round degree sequences {total}, realisable on the circle {feasible}")
        for d in failures[:5]:
            print("   not realisable:", d)

    # cross-check for n <= 5: realisable tournaments, counted up to
    # isomorphism, coincide with locally transitive ones
    for n in range(3, 6):
        lt = set()
        for edges in itertools.product([0, 1], repeat=n * (n - 1) // 2):
            beats = set()
            for (a, b), e in zip(itertools.combinations(range(n), 2), edges):
                beats.add((a, b) if e else (b, a))
            if locally_transitive(beats, n):
                best = min(tuple(sorted((p[a], p[b]) for a, b in beats))
                           for p in itertools.permutations(range(n)))
                lt.add(best)
        circ = set()
        for d in itertools.product(range(n), repeat=n):
            if sum(d) == n * (n - 1) // 2 and is_tournament(d, n) and realisable(d, n):
                circ.add(canonical(d, n))
        print(f"n={n}: locally transitive classes {len(lt)}, circle-realisable classes {len(circ)}, equal: {lt == circ}")
