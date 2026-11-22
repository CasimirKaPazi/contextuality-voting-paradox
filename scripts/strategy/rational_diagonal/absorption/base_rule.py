"""The base cases by hand: a line of j with outcome x makes an invalid form valid.
(A) fewer than three outcomes before (x new): P = (u, x, v), u not forced by j before.
(B) a dictator before (the other player): any P with top and bottom different from x.
In both cases Q is the reverse of P.  Checked on stopping games (all suffix transitions)."""
import pickle, sys
from itertools import permutations
from sg import present, valid, forces, works_direct
k = int(sys.argv[1]); N = int(sys.argv[2])
data = pickle.load(open(f"data_k{k}_N{N}.pkl", "rb"))
checked = bad = 0
for p, o, z, W in data:
    G1 = (p[1:], o[1:], z)
    if len(p) < 1 or valid(*G1): continue
    j, x = p[0], o[0]
    pr1 = present(G1[1], z); pr = present(o, z)
    if len(pr1) < 3:
        assert x not in pr1 and len(pr1) == 2
        Fj = forces(*G1, j)
        for u in pr1 - Fj:
            v = (pr1 - {u}).pop(); P = (u, x, v)
            checked += 1; bad += not works_direct(p, o, z, j, P, P[::-1])
    else:
        assert forces(*G1, 1 - j) == pr1 and forces(*G1, j) != pr1
        for P in permutations(sorted(pr)):
            if P[0] != x and P[-1] != x:
                checked += 1; bad += not works_direct(p, o, z, j, P, P[::-1])
print(f"k={k}: {checked} orders checked at base transitions, {bad} failures")
