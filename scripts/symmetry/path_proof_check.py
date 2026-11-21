"""Numerical check of the hand proof: completion by any linear extension of the voter's path
pattern, plus 'a3 above a1' when the pattern puts a2 above both or below both of a1, a3.
For random weights over all path patterns (some zero), the minimum and maximum of P(a1>...>am)
over all laws on rankings with the mixture's (m-1)-alternative marginals must coincide with the
weight of the all-ones pattern."""
import itertools, random, numpy as np
from scipy.optimize import linprog
def run(m, trials=30):
    alts = "abcdefgh"[:m]; R = ["".join(r) for r in itertools.permutations(alts)]
    S = [(alts[i], alts[i + 1]) for i in range(m - 1)]
    def ok(r, p):
        if not all((r.index(u) < r.index(v)) == bool(b) for (u, v), b in zip(S, p)): return False
        if p[0] != p[1] and not (r.index("c") < r.index("a")): return False   # a3 above a1
        return True
    rng = random.Random(m)
    pats = list(itertools.product((0, 1), repeat=m - 1))
    subs = list(itertools.combinations(alts, m - 1))
    def restr(r, T): return "".join(c for c in r if c in T)
    target = "".join(alts); worst = 0
    for _ in range(trials):
        rule = {p: rng.choice([r for r in R if ok(r, p)]) for p in pats}   # a random admissible linear extension
        w = np.array([rng.random() * (rng.random() < 0.7) for _ in pats]); w = w / w.sum()
        A, b = [], []
        for T in subs:
            for o in itertools.permutations(T):
                o = "".join(o)
                A.append([1.0 if restr(r, T) == o else 0.0 for r in R])
                b.append(sum(wk for p, wk in zip(pats, w) if restr(rule[p], T) == o))
        c = np.array([1.0 if r == target else 0.0 for r in R])
        lo = linprog(c, A_eq=A, b_eq=b, bounds=(0, None), method="highs").fun
        hi = -linprog(-c, A_eq=A, b_eq=b, bounds=(0, None), method="highs").fun
        mix = w[pats.index((1,) * (m - 1))]
        worst = max(worst, hi - lo, abs(lo - mix))
    print(f"m={m}: {trials} random completions and weights, largest deviation {worst:.2e}")
run(4); run(5); run(6, trials=5)
