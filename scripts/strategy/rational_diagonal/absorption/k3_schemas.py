"""Group the learned clauses into schemas valid under every renaming of outcomes (and for both
players), on all three-outcome stopping games up to 7 nodes; then minimise the set of schemas
needed for the lemma."""
import pickle, itertools
from sg import matrix
from k3_feat import feats
exec(open("k3_cegar.py").read().split("V = set()")[0])   # names, idx, NV, data
Vall = set()
for p, o, z, W in data:
    if len(set(o) | {z}) != 3: continue
    for j in (0, 1):
        fj, fd = feats(matrix(p, o, z, j)), feats(matrix(p, o, z, 1 - j))
        Vall.add(vec(fj, fd))
print(len(Vall), "vectors (all games, both roles; renamings are covered by the schema test)")
names_, learned = pickle.load(open("k3_learned.pkl", "rb"))
def ren(n, pi):
    pl, kind, *us = n; return (pl, kind, *[pi[u] for u in us])
def instances(cl):
    out = set()
    for pi in itertools.permutations(range(3)):
        out.add(tuple(sorted((idx[ren(names[i], pi)], val) for i, val in cl)))
    return out
def valid(cl): return all(any(v[i] == val for i, val in cl) for v in Vall)
schemas = []
for cl in learned:
    inst = instances(cl)
    ok = all(valid(c) for c in inst)
    schemas.append((cl, inst, ok))
def show(cl): return " or ".join(("" if val else "not ") + "_".join(map(str, names[i])) for i, val in cl)
for cl, inst, ok in schemas: print("schema-valid" if ok else "ONLY LABELLED", " ", show(cl))
pickle.dump([(cl, ok) for cl, inst, ok in schemas], open("k3_schemas.pkl", "wb"))
