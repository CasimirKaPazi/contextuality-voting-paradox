"""The recombination property (R): for any two cells x = (r, s0) and y = (r0, s) there is a row r'
with (r', s0) = g(x) and (r', s) = g(y), or a column s' with (r, s') = g(x) and (r0, s') = g(y).
Checks: (R) on game trees; and the chain with three outcomes, and piece 2 with more, on random tight
forms with (R)."""
import random, itertools, sys, collections
sys.path.insert(0, "../absorption")
from k3_chain import T, forces, tt
from chain_pairs import check, valid
from tightforms import tight
from pi_trees import rand_tree, normal_form
def recomb(R):
    n, m = len(R), len(R[0])
    for r, s0, r0, s in itertools.product(range(n), range(m), range(n), range(m)):
        gx, gy = R[r][s0], R[r0][s]
        if any(R[q][s0] == gx and R[q][s] == gy for q in range(n)): continue
        if any(R[r][t] == gx and R[r0][t] == gy for t in range(m)): continue
        return False
    return True
if __name__ == "__main__":
    random.seed(11); st = collections.Counter()
    g = 0
    while g < 300:
        t = rand_tree(random.randint(3, 5), random.choice((3, 4))); R = normal_form(t)
        if R is None: continue
        g += 1; st["trees"] += 1; st["trees without (R)"] += not recomb(R)
    for k in (3, 4):
        g = 0; tries = 0
        while g < 400 and tries < 3 * 10**6:
            tries += 1
            n, m = random.randint(2, 6), random.randint(2, 6)
            R = [[random.randrange(k) for _ in range(m)] for _ in range(n)]
            for _ in range(random.randint(0, 2 * n * m)):
                i, j = random.randrange(n), random.randrange(m)
                R[i][j] = R[i][random.randrange(m)] if random.random() < .5 else R[random.randrange(n)][j]
            if not valid(R, k) or tt(R) or not tight(R, k) or not recomb(R): continue
            g += 1; s2 = collections.Counter(); check(R, k, s2)
            st[(k, "tight forms with (R), not totally tight")] += 1
            for key in ("cases", "chain fails", "(ii) violated"): st[(k, key)] += s2[key]
    for key in sorted(st, key=str): print(key, st[key])
