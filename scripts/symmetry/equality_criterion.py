"""The Equality Criterion (Wolk, Quinn and Ogren 2023) on strict-ranking ballots.

A rule passes if adding any ballot b together with its reverse never changes the outcome (for lottery
outputs: the distribution). Checked on random profiles for four alternatives, with ties split evenly:
plurality, Borda, antiplurality, the symmetric positional rule (1, 1, 0, 0), Minimax, maximal lotteries,
random ballot (lottery over winners) and uniform random dictatorship (lottery over rankings).
Also the necessity argument for positional rules: on the profile of all m! rankings every candidate ties,
and adding b with its reverse gives candidate c the extra score w_k + w_(m+1-k), k = c's position in b.
Run: python3 equality_criterion.py   (needs numpy and scipy)
"""
import itertools
import random
import numpy as np
from scipy.optimize import linprog

random.seed(5)
M = 4
RANKS = list(itertools.permutations(range(M)))


def positional(w):
    def rule(p):
        s = np.zeros(M)
        for r in p:
            for k, c in enumerate(r): s[c] += w[k]
        top = np.flatnonzero(np.isclose(s, s.max()))
        out = np.zeros(M); out[top] = 1 / len(top); return out
    return rule


def margins(p):
    G = np.zeros((M, M))
    for r in p:
        for i, a in enumerate(r):
            for b in r[i + 1:]: G[a, b] += 1; G[b, a] -= 1
    return G


def minimax(p):
    worst = np.maximum(margins(p), 0).max(0)            # largest defeat of each candidate
    top = np.flatnonzero(np.isclose(worst, worst.min()))
    out = np.zeros(M); out[top] = 1 / len(top); return out


def maximal_lottery(p):
    G = margins(p)                                       # find x >= 0, sum 1, with x^T G >= 0
    res = linprog(np.zeros(M), A_ub=-G.T, b_ub=np.zeros(M), A_eq=np.ones((1, M)), b_eq=[1],
                  bounds=(0, 1), method="highs")
    return np.round(res.x, 9)                            # unique for an odd electorate


def random_ballot(p):
    out = np.zeros(M)
    for r in p: out[r[0]] += 1 / len(p)
    return out


def random_dictatorship(p):                              # lottery over rankings
    out = np.zeros(len(RANKS))
    for r in p: out[RANKS.index(r)] += 1 / len(p)
    return out


RULES = {"plurality (1,0,0,0)": positional([1, 0, 0, 0]), "Borda (3,2,1,0)": positional([3, 2, 1, 0]),
         "antiplurality (1,1,1,0)": positional([1, 1, 1, 0]), "symmetric (1,1,0,0)": positional([1, 1, 0, 0]),
         "Minimax": minimax, "maximal lotteries": maximal_lottery, "random ballot": random_ballot,
         "uniform random dictatorship": random_dictatorship}


def check(rule, trials=2000):
    for _ in range(trials):
        n = random.randrange(1, 8, 2) if rule is maximal_lottery else random.randint(1, 8)
        p = [random.choice(RANKS) for _ in range(n)]
        b = random.choice(RANKS)
        if not np.allclose(rule(p), rule(p + [b, b[::-1]])): return False
    return True


if __name__ == "__main__":
    print("Random profiles, four alternatives: passes the Equality Criterion?")
    for name, rule in RULES.items():
        print(f"  {name:30s} {check(rule)}")
    print("All 24 rankings once each, plus b and its reverse: extra score per candidate")
    for name, w in [("plurality", [1, 0, 0, 0]), ("Borda", [3, 2, 1, 0]), ("antiplurality", [1, 1, 1, 0]),
                    ("symmetric (1,1,0,0)", [1, 1, 0, 0])]:
        b = RANKS[0]; extra = [w[b.index(c)] + w[M - 1 - b.index(c)] for c in range(M)]
        print(f"  {name:22s} extra scores {extra}; winners change: "
              f"{not np.allclose(positional(w)(RANKS), positional(w)(list(RANKS) + [b, b[::-1]]))}")
