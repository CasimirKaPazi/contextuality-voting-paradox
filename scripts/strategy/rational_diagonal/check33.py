from diag2 import *
from itertools import product, permutations
import random
outs = "abc"; prefs = list(permutations(outs))
tot = fails = 0; mism = 0
for g in product(outs, repeat=9):
    if set(g) != set(outs) or dictator(g, 3, 3, outs): continue
    tot += 1
    f = works_fast(g, 3, 3, outs, prefs)
    if f is None: fails += 1
    if tot % 50 == 0:
        if (works_brute(g,3,3,outs,prefs) is None) != (f is None): mism += 1
print(tot, fails, "mismatches on sample:", mism)
