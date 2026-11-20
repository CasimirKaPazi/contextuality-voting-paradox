"""
Participation (no-show paradox) in the vote-share picture.

Adding voters with ballot B moves the profile x along the segment towards the vertex e_B.
If adding any number of such voters must never make the outcome worse for them, the winner must
improve (weakly, in B's ranking) along every such segment. A violation is a pair s1 < s2 on the
segment where the winner at s2 is ranked lower by B than the winner at s1.

For each rule and number of candidates: count violations along random segments, and record for
each violation whether the starting point had a majority cycle and how the new winner relates to
the old one.
"""
import numpy as np
from itertools import permutations

rng = np.random.default_rng(4)

def margins(shares, orders, n):
    M = np.zeros((n, n))
    for s, o in zip(shares, orders):
        r = np.empty(n, int); r[list(o)] = np.arange(n)
        M += s * np.sign(r[None, :] - r[:, None])       # +s where row is ranked above column
    return M

def condorcet_winner(M):
    n = len(M)
    for i in range(n):
        if all(M[i, j] > 0 for j in range(n) if j != i): return i
    return None

def maximin(M, p, orders, n):
    return int(np.argmax([min(M[i, j] for j in range(n) if j != i) for i in range(n)]))

def borda(M, p, orders, n):
    sc = np.zeros(n)
    for s, o in zip(p, orders):
        for k, c in enumerate(o): sc[c] += s * (n - 1 - k)
    return int(np.argmax(sc))

def black(M, p, orders, n):
    w = condorcet_winner(M)
    return w if w is not None else borda(M, p, orders, n)

RULES = {"maximin": maximin, "Black": black, "Borda": borda}
STEPS = np.linspace(0, 0.6, 121)

for n in (3, 4):
    orders = list(permutations(range(n)))
    for name, rule in RULES.items():
        viol = from_cycle = segments = 0
        kinds = {}
        while segments < 1500:
            x = rng.dirichlet(np.ones(len(orders)) * 0.5)
            b = rng.integers(len(orders)); B = orders[b]
            rank = {c: k for k, c in enumerate(B)}
            e = np.zeros(len(orders)); e[b] = 1
            segments += 1
            best_so_far = None; start_cycle = None
            for s in STEPS:
                p = (1 - s) * x + s * e
                M = margins(p, orders, n)
                w = rule(M, p, orders, n)
                if best_so_far is None:
                    best_so_far = w; start_cycle = condorcet_winner(M) is None
                    w0_cycle = start_cycle
                elif rank[w] > rank[best_so_far]:
                    viol += 1
                    cyc_here = condorcet_winner(margins((1 - s + 0.005) * x + (s - 0.005) * e, orders, n)) is None
                    from_cycle += cyc_here
                    key = f"B ranks old winner {rank[best_so_far] + 1}, new winner {rank[w] + 1}"
                    kinds[key] = kinds.get(key, 0) + 1
                    break
                elif rank[w] < rank[best_so_far]:
                    best_so_far = w
        print(f"n={n} {name:8s}: violations on {viol}/{segments} segments; "
              f"just before the violation a cycle was present in {from_cycle}/{viol}")
        for k, v in sorted(kinds.items(), key=lambda kv: -kv[1])[:4]:
            print(f"      {v:4d}  {k}")
