"""
Consistency (reinforcement) as convexity of winner regions.

Profiles for three candidates are vote shares over the six strict rankings (a point of the
5-simplex). Joining two electorates gives a weighted average of their share vectors. So a rule is
consistent iff, whenever W(P) = W(Q) = w, also W(tP + (1-t)Q) = w for t in (0, 1).

For each rule: sample pairs P, Q with the same winner, test random mixtures, record violations,
and record whether P or Q lies in the majority-cycle region.
Shares are continuous (large-electorate limit), so exact ties have probability zero.
"""
import numpy as np
from itertools import permutations

rng = np.random.default_rng(1)
C = "abc"
ORDERS = list(permutations(C))
pos = {x: np.array([o.index(x) for o in ORDERS]) for x in C}

def margins(p):
    # m[x][y] = share ranking x above y minus share ranking y above x
    return {x: {y: float(p @ np.where(pos[x] < pos[y], 1, -1)) for y in C if y != x} for x in C}

def condorcet_winner(m):
    for x in C:
        if all(m[x][y] > 0 for y in m[x]): return x
    return None

def borda(p, m=None):
    return max(C, key=lambda x: p @ (2 - pos[x]))

def plurality(p, m=None):
    return max(C, key=lambda x: p @ (pos[x] == 0))

def maximin(p, m=None):        # = ranked pairs = Schulze for three candidates
    m = m or margins(p)
    return max(C, key=lambda x: min(m[x].values()))

def black(p, m=None):           # Condorcet winner, else Borda
    m = m or margins(p)
    return condorcet_winner(m) or borda(p)

def irv(p, m=None):
    first = {x: p @ (pos[x] == 0) for x in C}
    loser = min(C, key=lambda x: first[x])
    a, b = [x for x in C if x != loser]
    return a if p @ np.where(pos[a] < pos[b], 1, 0) > 0.5 else b

RULES = {"Borda": borda, "plurality": plurality, "maximin/RP/Schulze": maximin,
         "Black": black, "IRV": irv}

def in_cycle(p):
    return condorcet_winner(margins(p)) is None

N_PAIRS, N_MIX = 40000, 8
print(f"{'rule':20s} {'violations':>10s} {'share of pairs':>15s} {'violations with P or Q in a cycle':>34s}")
for name, W in RULES.items():
    viol = viol_cycle = tested = 0
    for _ in range(N_PAIRS):
        P, Q = rng.dirichlet(np.ones(6)), rng.dirichlet(np.ones(6))
        w = W(P)
        if W(Q) != w:
            continue
        tested += 1
        for t in rng.uniform(0, 1, N_MIX):
            if W(t * P + (1 - t) * Q) != w:
                viol += 1
                viol_cycle += in_cycle(P) or in_cycle(Q)
                break
    frac = viol / tested if tested else 0
    cyc = f"{viol_cycle}/{viol}" if viol else "-"
    print(f"{name:20s} {viol:10d} {frac:15.4f} {cyc:>34s}")
