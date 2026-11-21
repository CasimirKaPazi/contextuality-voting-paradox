"""n-player rational diagonal, brute force.
g: dict from strategy profiles (tuples) to outcomes; sizes m = (m1,...,mn)."""
from itertools import product, permutations
import sys

def profiles(m): return list(product(*[range(x) for x in m]))

def is_dictator(g, m, outs):
    n = len(m)
    for k in range(n):
        ok = True
        for o in outs:
            if not any(all(g[s] == o for s in profiles(m) if s[k] == t) for t in range(m[k])):
                ok = False; break
        if ok: return True
    return False

def br(g, m, s, k, rank):
    """is s[k] a best reply for k at s under rank (smaller better)"""
    v = rank[g[s]]
    return all(rank[g[s[:k] + (t,) + s[k+1:]]] >= v for t in range(m[k]))

def works(g, m, outs, i, P, Qs):
    rp = {x: j for j, x in enumerate(P)}
    rq = {k: {x: j for j, x in enumerate(Q)} for k, Q in Qs.items()}
    others = [k for k in range(len(m)) if k != i]
    for b in range(m[i]):
        found = False
        for c in product(*[range(m[k]) for k in others]):
            s = list(c); s.insert(i, b); s = tuple(s)
            if all(br(g, m, s, k, rq[k]) for k in others) and not br(g, m, s, i, rp):
                found = True; break
        if not found: return False
    return True

def any_works(g, m, outs):
    prefs = list(permutations(outs)); n = len(m)
    for i in range(n):
        others = [k for k in range(n) if k != i]
        for P in prefs:
            for Qt in product(prefs, repeat=len(others)):
                if works(g, m, outs, i, P, dict(zip(others, Qt))): return (i, P, Qt)
    return None

if __name__ == "__main__":
    m = tuple(map(int, sys.argv[1].split("x"))); k = int(sys.argv[2])
    outs = "abcdefg"[:k]; prof = profiles(m)
    tot = fails = 0
    for vals in product(outs, repeat=len(prof)):
        if vals[0] != 'a' or set(vals) != set(outs): continue
        g = dict(zip(prof, vals))
        if is_dictator(g, m, outs): continue
        tot += 1
        if any_works(g, m, outs) is None:
            fails += 1
            if fails <= 5: print("FAIL", vals)
    print(m, k, "total", tot, "fails", fails)
