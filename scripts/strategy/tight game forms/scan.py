import sys
from diag2 import *
from itertools import product, permutations
m1, m2, k = map(int, sys.argv[1:4])
outs = "abcdefg"[:k]; prefs = list(permutations(outs))
tot = fails = 0; ex = []
for g in product(outs, repeat=m1*m2):
    if set(g) != set(outs): continue
    if g[0] != 'a': continue          # relabel outcomes: first cell is 'a' (symmetry)
    if dictator(g, m1, m2, outs): continue
    tot += 1
    if works_fast(g, m1, m2, outs, prefs) is None:
        fails += 1
        if len(ex) < 5: ex.append(g)
print(m1, m2, k, "forms (first cell a):", tot, "fails:", fails)
for g in ex:
    for a in range(m1): print("  ", " ".join(g[a*m2:(a+1)*m2]))
    print()
