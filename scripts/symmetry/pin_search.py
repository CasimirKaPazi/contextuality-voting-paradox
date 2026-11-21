"""For a set S of three pairs among four alternatives (a star or a path), look for a completion:
a rule assigning to each pattern of a voter's bits on S a full ranking, such that at the
resulting profile the four triple laws (each the mixture law of the voters' restricted rankings)
force the law of the social bits on S.  Since the law on S depends only on the columns of S,
a pinning completion shows the law on S is the mixture law at every profile."""
import sys, random, itertools
import numpy as np
from scipy.optimize import linprog
alts = "abcd"; R = list(itertools.permutations(alts))
pos = [{x: i for i, x in enumerate(r)} for r in R]
triples = list(itertools.combinations(alts, 3))
def bits(p, S): return tuple(int(p[u] < p[v]) for u, v in S)
def restr(p, T): return tuple(sorted(T, key=lambda x: p[x]))
def lp_range(voter_ranks, w, S, pattern):
    """min and max of P(social bits on S = pattern) over laws on rankings with the given triple marginals"""
    A, b = [], []
    for T in triples:
        for o in itertools.permutations(T):
            A.append([1.0 if restr(p, T) == o else 0.0 for p in pos])
            b.append(sum(wk for rk, wk in zip(voter_ranks, w) if restr(pos[rk], T) == o))
    A.append([1.0] * len(R)); b.append(1.0)
    c = np.array([1.0 if bits(p, S) == pattern else 0.0 for p in pos])
    lo = linprog(c, A_eq=A, b_eq=b, bounds=(0, None), method="highs")
    hi = linprog(-c, A_eq=A, b_eq=b, bounds=(0, None), method="highs")
    return lo.fun, -hi.fun
def search(S):
    patterns = sorted({bits(p, S) for p in pos})
    options = {pt: [i for i, p in enumerate(pos) if bits(p, S) == pt] for pt in patterns}
    random.seed(0)
    w = np.random.default_rng(0).dirichlet(np.ones(len(patterns)))
    found = {}
    for target in patterns:
        for choice in itertools.product(*[options[pt] for pt in patterns]):
            lo, hi = lp_range(list(choice), w, S, target)
            if hi - lo < 1e-9:
                found[target] = dict(zip(patterns, choice)); break
        else:
            found[target] = None
    return patterns, found
def check(S, rule, target, trials=300):
    """does the same rule pin the event for random weights, with random patterns absent?"""
    rng = np.random.default_rng(1); patterns = list(rule)
    for _ in range(trials):
        w = rng.dirichlet(np.ones(len(patterns))) * (rng.random(len(patterns)) < 0.6)
        if w.sum() == 0: continue
        w = w / w.sum()
        lo, hi = lp_range([rule[pt] for pt in patterns], w, S, target)
        mix = sum(wk for pt, wk in zip(patterns, w) if pt == target)
        if hi - lo > 1e-7 or abs(lo - mix) > 1e-7: return False
    return True
for name, S in [("star", (("a", "b"), ("a", "c"), ("a", "d"))), ("path", (("a", "b"), ("b", "c"), ("c", "d")))]:
    patterns, found = search(S)
    for t in patterns:
        rule = found[t]
        if rule is None: print(name, t, "NOT pinned by any completion"); continue
        ok = check(S, rule, t)
        print(name, t, "pinned; robust:", ok, " rule:", {pt: "".join(R[i]) for pt, i in rule.items()})
