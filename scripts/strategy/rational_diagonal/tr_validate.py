"""Cross-check the summary automaton against the matrix computation on random line sequences."""
import random, sys
sys.argv = ["x", sys.argv[1]]
exec(open("tr_automaton.py").read().split("seen = set()")[0])
from recipes_core import works_PQ
from diag2 import dictator
random.seed(1); mism = 0; checked = 0
for trial in range(3000):
    z = random.randrange(k); M = [[z]]
    s = (tuple(bit(z, z) for _ in configs), 1 << z, (1 << z, 1 << z))
    for _ in range(random.randint(1, 9)):
        j, o = random.randrange(2), random.randrange(k)
        if j == 0: M.insert(0, [o] * len(M[0]))
        else: [r.insert(0, o) for r in M]
        s = step(s, j, o)
        used = sorted({x for r in M for x in r})
        g = tuple(x for r in M for x in r)
        assert (len(used) >= 3 and not dictator(g, len(M), len(M[0]), used)) == valid(s)
        A = set(works(s)); checked += 1
        for (i, a, b) in configs:
            R = M if i == 0 else [list(c) for c in zip(*M)]
            if works_PQ(R, prefs[a], prefs[b]) != ((i, a, b) in A): mism += 1
print(f"{checked} forms checked, {mism} mismatches")
