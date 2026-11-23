"""Games of perfect information (trees): are their normal forms totally tight, and do the chain,
the theorem's two kinds, and a rational diagonal at all hold?  Random trees with k outcomes."""
import random, itertools, sys, collections
sys.path.insert(0, "../absorption")
from k3_chain import works, T, forces, tt
def rand_tree(depth, k):
    if depth == 0 or random.random() < 0.25: return ("leaf", random.randrange(k))
    return ("node", random.randrange(2), [rand_tree(depth - 1, k) for _ in range(random.choice((2, 2, 3)))])
def nodes(t, pl):
    if t[0] == "leaf": return []
    out = [t] if t[1] == pl else []
    for c in t[2]: out += nodes(c, pl)
    return out
def play(t, s0, s1):
    while t[0] == "node":
        s = s0 if t[1] == 0 else s1
        t = t[2][s[id(t)]]
    return t[1]
def strategies(t, pl):
    ns = nodes(t, pl)
    for ch in itertools.product(*[range(len(n[2])) for n in ns]):
        yield {id(n): c for n, c in zip(ns, ch)}
def normal_form(t):
    from math import prod
    n0 = prod(len(n[2]) for n in nodes(t, 0)); n1 = prod(len(n[2]) for n in nodes(t, 1))
    if n0 * n1 > 400: return None
    S0 = list(strategies(t, 0)); S1 = list(strategies(t, 1))
    R = [[play(t, a, b) for b in S1] for a in S0]
    # remove duplicate rows/columns
    R = [list(r) for r in dict.fromkeys(tuple(r) for r in R)]
    C = [list(c) for c in dict.fromkeys(tuple(c) for c in T(R))]
    return T(C)
def valid(R, k):
    return len({v for r in R for v in r}) == k and not any(all(forces(M, u) for u in range(k)) for M in (R, T(R)))
def kinds_work(R, k):
    for Ri in (R, T(R)):
        for P in itertools.permutations(range(k)):
            if works(Ri, P, P[::-1]) or works(Ri, P, P[1:] + P[:1]): return True
    return False
def any_diag(R, k):
    for Ri in (R, T(R)):
        for P in itertools.permutations(range(k)):
            for Q in itertools.permutations(range(k)):
                if works(Ri, P, Q): return True
    return False
def chain(R, k):
    cases = fails = 0
    for Ri, Ro in ((R, T(R)), (T(R), R)):
        for a, c in itertools.permutations(range(k), 2):
            if forces(Ri, a) or forces(Ro, c): continue
            for mid in itertools.permutations([u for u in range(k) if u not in (a, c)]):
                P = (a,) + mid + (c,); rP = P[::-1]; P1 = (a,) + rP[:-1]; P2 = (c,) + P[:-1]
                cases += 1
                fails += not (works(Ri, P, rP) or works(Ro, rP, P) or works(Ri, P1, rP) or works(Ro, P2, P))
    return cases, fails
if __name__ == "__main__":
    random.seed(1); st = collections.Counter()
    for k in (3, 4):
        g = 0
        while g < (600 if k == 3 else 300):
            t = rand_tree(random.randint(3, 5), k); R = normal_form(t)
            if R is None or not valid(R, k): continue
            g += 1; ttf = tt(R)
            c, f = chain(R, k)
            key = (k, "totally tight" if ttf else "not totally tight")
            st[key + ("forms",)] += 1; st[key + ("chain cases",)] += c; st[key + ("chain failures",)] += f
            st[key + ("forms with a chain failure",)] += f > 0
            kw = kinds_work(R, k); st[key + ("two kinds fail",)] += not kw
            if not kw: st[key + ("no rational diagonal at all",)] += not any_diag(R, k)
    for key in sorted(st): print(key, st[key])
