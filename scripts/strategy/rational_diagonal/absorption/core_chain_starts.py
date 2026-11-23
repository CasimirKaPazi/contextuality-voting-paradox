"""Pessimistic starting summaries from the cores, for the four configurations of the chain, with any
number of outcomes that nobody forces.  Generalises core_struct4.py (Section 4): the three key
outcomes follow the table of Fig. 13; the outcomes nobody forces (the set E) occur only in the
recursive blocks, where the last two classes meet, and there any cell may hold any key outcome or any
outcome of E.  Lines of class 0123 hold the three keys and possibly outcomes of E; lines of class
1234 hold the three keys and at least one outcome of E.

Outcomes are 0..k-1 with P = (0, ..., k-1) for the chain; every assignment of the keys to three
outcomes and every set E of further outcomes is used; the rest can be added later by lines.
For each line the possible pairs (y, M) are collected: y is the opponent's favourite in the line's
content S, and M ranges over the best outcomes (for the line's owner) that a column holding y in the
line can contain.  This is a superset of the true pairs (pessimistic, Section 3).
Output: one start per line, 'present m0 m1 m2 m3' (bit y*k+M per configuration).
Usage: python3 core_chain_starts.py k > starts_k.txt"""
import sys
from itertools import permutations, combinations, product
k = int(sys.argv[1])
P = tuple(range(k)); rP = P[::-1]; Ps = (0,) + rP[:-1]; rPs = (k - 1,) + P[:-1]
CFG = [(0, P, rP), (1, rP, P), (0, Ps, rP), (1, rPs, P)]    # (player, own order, opponent order)
RK = [({u: n for n, u in enumerate(own)}, {u: n for n, u in enumerate(opp)}) for _, own, opp in CFG]
CL = ["13", "12", "23", "1123", "1223", "3123", "0123", "1234"]
REC = {"0123", "1234"}
Traw = {
 "13":   ["1", "1", "3", "1", "1", "13", "1", "1"],
 "12":   ["1", "2", "2", "12", "2", "2", "2", "2"],
 "23":   ["3", "2", "3", "3", "23", "3", "3", "3"],
 "1123": ["1", "12", "3", "1", "1", "3", "13", "1"],
 "1223": ["1", "2", "23", "1", "2", "2", "12", "2"],
 "3123": ["13", "2", "3", "3", "2", "3", "23", "3"],
 "0123": ["1", "2", "3", "13", "12", "23", "*", "*"],
 "1234": ["1", "2", "3", "1", "2", "3", "*", "*"],
}
def subsets(s):
    s = sorted(s)
    for r in range(len(s) + 1):
        for c in combinations(s, r): yield frozenset(c)
def starts_for(keys, E):
    K = frozenset(keys); kmap = {"1": keys[0], "2": keys[1], "3": keys[2]}
    def allowed(rc, c):
        t = Traw[rc][CL.index(c)]
        return K | E if t == "*" else frozenset(kmap[ch] for ch in t)
    def contents(c):            # possible contents of a line of class c
        if c in ("13", "12", "23"): return [frozenset(kmap[ch] for ch in c)]
        if c in ("1123", "1223", "3123"): return [K]
        if c == "0123": return [K | X for X in subsets(E)]
        return [K | X for X in subsets(E) if X]
    cache = {}
    def line_pairs(cfg, rc, cols):
        key = (cfg, rc, cols)
        if key in cache: return cache[key]
        rp, rq = RK[cfg]; out = 0
        for S in contents(rc):
            if not (S - K) <= frozenset().union(*(allowed(rc, c) for c in cols)) - K: continue
            if any(not (allowed(rc, c) & S) for c in cols): continue
            if not S <= frozenset().union(*(allowed(rc, c) & S for c in cols)): continue
            y = min(S, key=lambda u: rq[u])
            forced = [c for c in cols if allowed(rc, c) & S == {y}]
            optional = [c for c in cols if y in allowed(rc, c) and c not in forced]
            def cands(c):   # possible best outcomes (for the owner) of a column of class c holding y
                return {min(cont, key=lambda u: rp[u]) for cont in contents(c) if y in cont}
            for r in range(len(optional) + 1):
                for extra in combinations(optional, r):
                    B = forced + list(extra)
                    if not B: continue
                    best = None
                    for c in B:
                        cs = cands(c)
                        if not cs: best = set(); break
                        best = cs if best is None else {min(a, b, key=lambda u: rp[u]) for a in best for b in cs}
                    for M in best or ():
                        out |= 1 << (y * k + M)
        cache[key] = out
        return out
    res = set(); opt = CL[3:]
    for rmask in range(32):
        R = tuple(CL[:3] + [opt[j] for j in range(5) if rmask >> j & 1])
        for cmask in range(32):
            C = tuple(CL[:3] + [opt[j] for j in range(5) if cmask >> j & 1])
            rec = bool(REC & set(R)) and bool(REC & set(C))
            if E and not rec: continue
            if not rec and ("1234" in R or "1234" in C): continue
            m = []
            for cfg, (pl, _, _) in enumerate(CFG):
                lines, opp = (R, C) if pl == 0 else (C, R)
                v = 0
                for rc in lines: v |= line_pairs(cfg, rc, opp)
                m.append(v)
            if all(m):
                res.add((sum(1 << u for u in K | E), *m))
    return res
allst = set()
for keys in permutations(range(k), 3):
    rest = [u for u in range(k) if u not in keys]
    for r in range(len(rest) + 1):
        for E in combinations(rest, r):
            allst |= starts_for(keys, frozenset(E))
for s in sorted(allst): print(*s)
print(len(allst), "starting summaries", file=sys.stderr)
