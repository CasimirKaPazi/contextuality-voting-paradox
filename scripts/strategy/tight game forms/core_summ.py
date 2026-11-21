"""Joint row-type summaries (family zsrot, k outcomes) of the cores listed in the given files."""
import sys
from itertools import permutations
k = int(sys.argv[1]); prefs = list(permutations(range(k)))
rank = [{x: r for r, x in enumerate(p)} for p in prefs]
cfgs = [(i, a, b) for i in (0, 1) for a in range(len(prefs)) for b in range(len(prefs))
        if prefs[b] == prefs[a][::-1] or prefs[b] == prefs[a][1:] + prefs[a][:1]]
def summary(M, i, a, b):
    R = M if i == 0 else [list(c) for c in zip(*M)]
    colbest = [min((r[c] for r in R), key=lambda x: rank[a][x]) for c in range(len(R[0]))]
    mask = 0
    for r in R:
        y = min(r, key=lambda x: rank[b][x])
        Mb = min((colbest[c] for c in range(len(r)) if r[c] == y), key=lambda x: rank[a][x])
        mask |= 1 << (y * k + Mb)
    return mask
seen = set()
for fn in sys.argv[2:]:
    for line in open(fn):
        M = [list(map(int, w)) for w in line.split()]
        present = 0
        for r in M:
            for x in r: present |= 1 << x
        key = (present, tuple(summary(M, *c) for c in cfgs))
        if key not in seen:
            seen.add(key); print(key[0], *key[1])
print(f"{len(seen)} distinct summaries", file=sys.stderr)
