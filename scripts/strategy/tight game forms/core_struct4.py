"""Like core_struct.py, but with a fourth outcome (index 3) that neither player can force,
following Fig. 13 including classes 1234 (lines containing the extra outcome) and the
recursive block 0123 x 0123.  Pessimistic choices: blocks among 0123/1234 may take any of the
four outcomes; columns of classes 0123 and 1234 may or may not contain the extra outcome."""
import sys
from itertools import permutations, product, combinations
k = 4; O = (0, 1, 2, 3)
prefs = list(permutations(O)); rank = [{x: r for r, x in enumerate(p)} for p in prefs]
cfgs = [(i, a, b) for i in (0, 1) for a in range(len(prefs)) for b in range(len(prefs))
        if prefs[b] == prefs[a][::-1] or prefs[b] == prefs[a][1:] + prefs[a][:1]]
CL = ["13", "12", "23", "1123", "1223", "3123", "0123", "1234"]
def v(s): return frozenset(int(c) - 1 for c in s)
T = {
 "13":   dict(zip(CL, map(v, ["1", "1", "3", "1", "1", "13", "1", "1"]))),
 "12":   dict(zip(CL, map(v, ["1", "2", "2", "12", "2", "2", "2", "2"]))),
 "23":   dict(zip(CL, map(v, ["3", "2", "3", "3", "23", "3", "3", "3"]))),
 "1123": dict(zip(CL, map(v, ["1", "12", "3", "1", "1", "3", "13", "1"]))),
 "1223": dict(zip(CL, map(v, ["1", "2", "23", "1", "2", "2", "12", "2"]))),
 "3123": dict(zip(CL, map(v, ["13", "2", "3", "3", "2", "3", "23", "3"]))),
 "0123": dict(zip(CL, map(v, ["1", "2", "3", "13", "12", "23", "1234", "1234"]))),
 "1234": dict(zip(CL, map(v, ["1", "2", "3", "1", "2", "3", "1234", "1234"]))),
}
contents = {"13": [v("13")], "12": [v("12")], "23": [v("23")]}
for c in ["1123", "1223", "3123"]: contents[c] = [v("123")]
contents["0123"] = [v("123"), v("1234")]; contents["1234"] = [v("1234")]
want = {"13": [v("13")], "12": [v("12")], "23": [v("23")], "1123": [v("123")], "1223": [v("123")],
        "3123": [v("123")], "0123": [v("123"), v("1234")], "1234": [v("1234")]}
def subsets(s):
    s = sorted(s)
    for r in range(1, len(s) + 1):
        for c in combinations(s, r): yield frozenset(c)
def rowchoices(rc, cols):
    """each choice: tuple over column classes of (value subset, column content)"""
    opts = [[(sub, cont) for sub in subsets(T[rc][c]) for cont in contents[c] if sub <= cont] for c in cols]
    for ch in product(*opts):
        S = frozenset().union(*(s for s, _ in ch))
        if S in want[rc]: yield S, ch
def rowtype(S, ch, a, bq):
    y = min(S, key=lambda x: rank[bq][x])
    M = y
    for sub, cont in ch:
        if y in sub:
            for w in cont: M = min((M, w), key=lambda z: rank[a][z])
    return 1 << (y * k + M)
def part(i, rows, cols):
    cf = [c for c in cfgs if c[0] == i]; vec = [0] * len(cf)
    for rc in rows:
        seen = set()
        for S, ch in rowchoices(rc, cols):
            key = (S, frozenset(ch))
            if key in seen: continue
            seen.add(key)
            vec = [m | rowtype(S, ch, a, bq) for m, (_, a, bq) in zip(vec, cf)]
    return vec
opt = CL[3:]
states = set()
for rmask in range(32):
    for cmask in range(32):
        R = CL[:3] + [opt[j] for j in range(5) if rmask >> j & 1]
        C = CL[:3] + [opt[j] for j in range(5) if cmask >> j & 1]
        present = 15 if ("1234" in R or "1234" in C or ("0123" in R and "0123" in C)) else 7
        states.add((present, *part(0, R, C), *part(1, C, R)))
for s in states: print(*s)
print(len(states), "initial summaries", file=sys.stderr)
