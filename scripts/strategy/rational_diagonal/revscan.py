import sys, random
from diag2 import rows_of, dictator
from itertools import product, permutations
from recipes_core import works_PQ
mode = sys.argv[1]
m1, m2, k = map(int, sys.argv[2:5])
outs = "abcdefg"[:k]; prefs = list(permutations(outs))
def rev_works(g):
    for i in (0, 1):
        R = rows_of(g, m1, m2, i)
        for P in prefs:
            if works_PQ(R, P, P[::-1]): return True
    return False
def gen():
    if mode == "all":
        for g in product(outs, repeat=m1*m2):
            if g[0] == 'a': yield g
    else:
        rnd = random.Random(int(sys.argv[5]))
        for _ in range(int(sys.argv[6])):
            yield tuple(rnd.choice(outs) for _ in range(m1*m2))
tot = fails = 0
for g in gen():
    if set(g) != set(outs) or dictator(g, m1, m2, outs): continue
    tot += 1
    if not rev_works(g):
        fails += 1
        if fails <= 3:
            print("FAIL"); [print("  ", " ".join(g[a*m2:(a+1)*m2])) for a in range(m1)]
print(mode, m1, m2, k, "total", tot, "rev fails", fails)
