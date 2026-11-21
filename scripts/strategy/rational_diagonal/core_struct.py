"""Core summaries from the block structure of irreducible totally tight forms
(Boros-Gurvich-Makino-Papp, Discrete Math. 310 (2010), Fig. 13, Approximation III), three outcomes.

Rows (and, symmetrically, columns) fall into classes 13, 12, 23 (non-empty; lines with exactly
that pair) and 1123, 1223, 3123, 0123 (possibly empty; lines with all three outcomes).  With only
three outcomes, rows 0123 and columns 0123 are not both non-empty.  Each block of the table lists
the outcomes its cells may take ("staircase" and two-valued blocks give two values).  A row's
contribution to the summary depends on its outcome set and, for each outcome u in it and each
other w, whether a u-cell lies in a column containing w; pair columns contain exactly their pair,
three-outcome columns contain all three.  For each pattern of non-empty classes we take the
union of all contributions any row of a present class can make (the most pessimistic case; the
summary is monotone in this union), for both players."""
import sys
from itertools import permutations, product, combinations
k = 3; O = (0, 1, 2)
prefs = list(permutations(O)); rank = [{x: r for r, x in enumerate(p)} for p in prefs]
cfgs = [(i, a, b) for i in (0, 1) for a in range(len(prefs)) for b in range(len(prefs))
        if prefs[b] == prefs[a][::-1] or prefs[b] == prefs[a][1:] + prefs[a][:1]]
A1, A2, A3 = 0, 1, 2
CL = ["13", "12", "23", "1123", "1223", "3123", "0123"]
def v(s): return frozenset(int(c) - 1 for c in s)
T = {  # T[row class][column class] = allowed outcomes (Fig. 13)
 "13":   dict(zip(CL, map(v, ["1", "1", "3", "1", "1", "13", "1"]))),
 "12":   dict(zip(CL, map(v, ["1", "2", "2", "12", "2", "2", "2"]))),
 "23":   dict(zip(CL, map(v, ["3", "2", "3", "3", "23", "3", "3"]))),
 "1123": dict(zip(CL, map(v, ["1", "12", "3", "1", "1", "3", "13"]))),
 "1223": dict(zip(CL, map(v, ["1", "2", "23", "1", "2", "2", "12"]))),
 "3123": dict(zip(CL, map(v, ["13", "2", "3", "3", "2", "3", "23"]))),
 "0123": dict(zip(CL, map(v, ["1", "2", "3", "13", "12", "23", "123"]))),
}
colset = {"13": v("13"), "12": v("12"), "23": v("23")}
for c in CL[3:]: colset[c] = v("123")
def subsets(s):
    s = sorted(s)
    for r in range(1, len(s) + 1):
        for c in combinations(s, r): yield frozenset(c)
def rowprofiles(rc, cols):
    """all (S, bits) a row of class rc can have when the column classes `cols` are non-empty"""
    out = set()
    for choice in product(*[list(subsets(T[rc][c])) for c in cols]):
        S = frozenset().union(*choice)
        want = {"13": v("13"), "12": v("12"), "23": v("23")}.get(rc, v("123"))
        if S != want: continue
        b = {(u, w): any(u in ch and w in colset[c] for ch, c in zip(choice, cols))
             for u in S for w in O if w != u}
        out.add((tuple(sorted(S)), tuple(sorted(b.items()))))
    return out
def rowtype(S, b, a, bq):
    y = min(S, key=lambda x: rank[bq][x]); x = prefs[a][0]
    if y == x or b[(y, x)]: M = x
    else: M = min((w for w in O if w != y and b[(y, w)]), key=lambda w: rank[a][w])
    M = min((M, y), key=lambda w: rank[a][w])
    return 1 << (y * k + M)
def part(i, rows, cols):
    cf = [c for c in cfgs if c[0] == i]; vec = [0] * len(cf)
    for rc in rows:
        for S, bits in rowprofiles(rc, cols):
            b = dict(bits)
            vec = [m | rowtype(S, b, a, bq) for m, (_, a, bq) in zip(vec, cf)]
    return vec
opt = CL[3:]
states = set()
for rmask in range(16):
    for cmask in range(16):
        R = CL[:3] + [opt[j] for j in range(4) if rmask >> j & 1]
        C = CL[:3] + [opt[j] for j in range(4) if cmask >> j & 1]
        if "0123" in R and "0123" in C: continue
        s = (7, *part(0, R, C), *part(1, C, R))   # the table is symmetric under transposition
        states.add(s)
for s in states: print(*s)
print(len(states), "initial summaries", file=sys.stderr)
