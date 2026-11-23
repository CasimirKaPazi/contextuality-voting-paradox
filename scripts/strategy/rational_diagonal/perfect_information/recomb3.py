"""Three outcomes: the chain lemma on random forms with the recombination property that are not
tight, and on forms without it."""
import random, itertools, sys, collections
sys.path.insert(0, "../absorption")
from k3_chain import T, forces, tt
from chain_pairs import valid
from tightforms import tight
from recomb import recomb
from pi_trees import chain
random.seed(13); st = collections.Counter(); k = 3
while st["(R), not tight: forms"] < 400 or st["no (R): forms"] < 400:
    n, m = random.randint(2, 6), random.randint(2, 6)
    R = [[random.randrange(k) for _ in range(m)] for _ in range(n)]
    for _ in range(random.randint(0, 2 * n * m)):
        i, j = random.randrange(n), random.randrange(m)
        R[i][j] = R[i][random.randrange(m)] if random.random() < .5 else R[random.randrange(n)][j]
    if not valid(R, k): continue
    rc = recomb(R)
    if rc and tight(R, k): continue
    key = "(R), not tight" if rc else "no (R)"
    if st[key + ": forms"] >= 400: continue
    c, f = chain(R, k); st[key + ": forms"] += 1; st[key + ": cases"] += c; st[key + ": chain failures"] += f
for key in sorted(st): print(key, st[key])
