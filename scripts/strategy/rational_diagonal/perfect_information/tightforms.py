"""The chain on random tight forms that are not totally tight."""
import random, itertools, sys, collections
sys.path.insert(0, "../absorption")
from k3_chain import works, T, forces, tt
from pi_trees import chain, valid, kinds_work
def tight(R, k):
    rows = [set(r) for r in R]; cols = [set(c) for c in T(R)]
    for m in range(1, 2 ** k - 1):
        S = {u for u in range(k) if m >> u & 1}
        if not (any(r <= S for r in rows) or any(c <= set(range(k)) - S for c in cols)): return False
    return True
if __name__ == "__main__":
  random.seed(3); st = collections.Counter()
  for k in (3, 4, 5):
      g = 0; tries = 0
      while g < (1500 if k < 5 else 300) and tries < 2 * 10**6:
          tries += 1
          n, m = random.randint(2, 6), random.randint(2, 6)
          R = [[random.randrange(k) for _ in range(m)] for _ in range(n)]
          for _ in range(random.randint(0, 2 * n * m)):
              i, j = random.randrange(n), random.randrange(m)
              R[i][j] = R[i][random.randrange(m)] if random.random() < .5 else R[random.randrange(n)][j]
          if not valid(R, k) or tt(R) or not tight(R, k): continue
          g += 1; c, f = chain(R, k)
          st[(k, "forms")] += 1; st[(k, "cases")] += c; st[(k, "failures")] += f; st[(k, "forms with failure")] += f > 0
          if f and not kinds_work(R, k): st[(k, "two kinds fail")] += 1
          if f and st[(k, "printed")] < 2: st[(k, "printed")] += 1; print(k, R)
  for key in sorted(st): print(key, st[key])
