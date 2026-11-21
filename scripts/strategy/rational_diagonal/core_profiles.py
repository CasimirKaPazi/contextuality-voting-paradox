"""Which row profiles occur in the enumerated three-outcome cores?  A profile of a row is its
outcome set S and, for u in S and w != u, whether a u-cell of the row lies in a column with w."""
import sys, collections
def profs(M):
    cols = [set(c) for c in zip(*M)]
    out = set()
    for r in M:
        S = tuple(sorted(set(r)))
        bits = tuple((u, w, any(r[c] == u and w in cols[c] for c in range(len(r))))
                     for u in S for w in range(3) if w != u)
        out.add((S, bits))
    return frozenset(out)
occ = collections.Counter(); sets = set()
for fn in sys.argv[1:]:
    for line in open(fn):
        M = [list(map(int, w)) for w in line.split()]
        for T in (M, [list(c) for c in zip(*M)]):
            p = profs(T); sets.add(p); occ.update(p)
print(len(occ), "profiles occur;", len(sets), "distinct profile sets")
for p, n in sorted(occ.items()): print(p, n)
mx = [s for s in sets if not any(s < t for t in sets)]
print(len(mx), "maximal profile sets, sizes", sorted(len(s) for s in mx))
import pickle; pickle.dump((sets, mx), open("profsets.pkl", "wb"))
