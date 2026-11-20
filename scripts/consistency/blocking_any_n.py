"""
No Condorcet extension is consistent, for any number of candidates: the blocking construction.

Vote shares over all strict rankings of n candidates. Take a profile x without a Condorcet winner
and suppose the rule elects a. Since a is not a Condorcet winner, some c beats a in x. Let y give
share 1/2 + d/2 to the ranking (a, c, rest) and 1/2 - d/2 to (c, a, rest). In y, a is the Condorcet
winner, and c beats every other candidate unanimously. For small d and suitable t, c is the
Condorcet winner of the mixture t*x + (1-t)*y, so a Condorcet extension must elect c there,
although it elects a in both parts.

The script constructs y and t explicitly for random profiles and random choices of a, and checks
that c is the Condorcet winner of the mixture.
"""
import numpy as np
from itertools import permutations

rng = np.random.default_rng(3)

def margin_matrix(shares, orders, n):
    M = np.zeros((n, n))
    for s, o in zip(shares, orders):
        rank = {c: i for i, c in enumerate(o)}
        for i in range(n):
            for j in range(n):
                if i != j:
                    M[i, j] += s if rank[i] < rank[j] else -s
    return M

def condorcet_winner(M):
    n = len(M)
    for i in range(n):
        if all(M[i, j] > 0 for j in range(n) if j != i):
            return i
    return None

for n in (3, 4, 5, 6):
    orders = list(permutations(range(n)))
    idx = {o: k for k, o in enumerate(orders)}
    tested = ok = 0
    while tested < 300:
        x = rng.dirichlet(np.ones(len(orders)) * 0.3)
        Mx = margin_matrix(x, orders, n)
        if condorcet_winner(Mx) is not None:
            continue
        a = rng.integers(n)                                   # whatever the rule elects
        c = int(np.argmax(Mx[:, a]))                          # a candidate beating a
        assert Mx[c, a] > 0
        rest = [k for k in range(n) if k not in (a, c)]
        worst = max(0.0, max((-Mx[c, d] for d in rest), default=0.0))   # how badly c loses to others in x
        t = 0.5 / (1 + worst)                                 # c beats every d in the mixture
        d = 0.5 * t * Mx[c, a] / (1 - t)                      # a's margin over c in y, small enough
        y = np.zeros(len(orders))
        y[idx[tuple([a, c] + rest)]] = 0.5 + d / 2
        y[idx[tuple([c, a] + rest)]] = 0.5 - d / 2
        My = margin_matrix(y, orders, n)
        z_winner = condorcet_winner(margin_matrix(t * x + (1 - t) * y, orders, n))
        tested += 1
        ok += (condorcet_winner(My) == a) and (z_winner == c)
    print(f"n={n}: {ok}/{tested} profiles without a Condorcet winner blocked as predicted")
