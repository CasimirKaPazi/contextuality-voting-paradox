"""More game trees: the chain, and piece 2 (no alpha with gamma), on normal forms of random trees."""
import random, itertools, sys, collections
sys.path.insert(0, "../absorption")
from pi_trees import rand_tree, normal_form, valid, chain
from k3_chain import T, forces, tt
from chain_pairs import check
random.seed(7); st = collections.Counter()
for k in (3, 4, 5):
    g = 0; tries = 0
    while g < (500 if k < 5 else 200) and tries < 200000:
        tries += 1
        t = rand_tree(random.randint(3, 6), k); R = normal_form(t)
        if R is None or not valid(R, k): continue
        g += 1; s2 = collections.Counter(); check(R, k, s2)
        st[(k, "forms")] += 1; st[(k, "not totally tight")] += not tt(R)
        for key in ("cases", "chain fails", "(ii) violated", "(iii) violated", "(iv) violated", "(i) violated"): st[(k, key)] += s2[key]
for key in sorted(st): print(key, st[key])
