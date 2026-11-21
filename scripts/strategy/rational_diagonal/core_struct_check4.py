"""Sanity check: the summary of every enumerated three-outcome core (up to 5x5) is covered,
bit by bit and after some renaming of outcomes, by one of the structural summaries."""
import sys
from itertools import permutations
exec(open("core_summ.py").read().split("seen = set()")[0].replace("k = int(sys.argv[1])", "k = 4"))
S = [tuple(map(int, l.split()))[1:] for l in open("core_struct4.txt")]
pidx = {p: n for n, p in enumerate(prefs)}
cidx = {c: n for n, c in enumerate(cfgs)}
def rename(vec, pi):
    out = [0] * len(cfgs)
    for n, (i, a, b) in enumerate(cfgs):
        m = vec[n]; mm = 0
        for t in range(16):
            if m >> t & 1: mm |= 1 << (pi[t // 4] * 4 + pi[t % 4])
        out[cidx[(i, pidx[tuple(pi[x] for x in prefs[a])], pidx[tuple(pi[x] for x in prefs[b])])]] = mm
    return out
bad = tot = 0
for fn in sys.argv[1:]:
    for line in open(fn):
        M = [list(map(int, w)) for w in line.split()]
        vec = [summary(M, *c) for c in cfgs]; tot += 1
        if not any(all(x & ~y == 0 for x, y in zip(rename(vec, pi), s)) for pi in permutations(range(4)) for s in S):
            bad += 1
print(tot, "cores,", bad, "not covered")
