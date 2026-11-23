"""The proved pieces 1-4 on random tight forms that are not totally tight."""
import random, sys, collections
sys.path.insert(0, "../absorption")
from k3_chain import T, forces, tt
from chain_pairs import check, valid
from tightforms import tight
random.seed(5); st = collections.Counter()
for k in (3, 4):
    g = 0
    while g < 800:
        n, m = random.randint(2, 6), random.randint(2, 6)
        R = [[random.randrange(k) for _ in range(m)] for _ in range(n)]
        for _ in range(random.randint(0, 2 * n * m)):
            i, j = random.randrange(n), random.randrange(m)
            R[i][j] = R[i][random.randrange(m)] if random.random() < .5 else R[random.randrange(n)][j]
        if not valid(R, k) or tt(R) or not tight(R, k): continue
        g += 1; s2 = collections.Counter(); check(R, k, s2)
        for key, v in s2.items(): st[(k, key)] += v
for key in sorted(st): print(key, st[key])
