"""Minimise the set of schemas (each closed under renaming outcomes) that refutes the negated lemma."""
import pickle, itertools
exec(open("k3_cegar.py").read().split("V = set()")[0])
src = open("k3_cegar.py").read()
exec(src[src.index("def lit("):src.index("learned = []")].replace("assert all(any(holds(g, v) for g in goods) for v in V)", ""))
sch = pickle.load(open("k3_schemas.pkl", "rb"))
def ren(n, pi): pl, kind, *us = n; return (pl, kind, *[pi[u] for u in us])
def inst(cl): return [[(idx[ren(names[i], pi)], val) for i, val in cl] for pi in itertools.permutations(range(3))]
S = [cl for cl, ok in sch if ok] + [[(idx[("j", "F", 0)], True), (idx[("d", "Esc", 0)], True)]]  # j forces u or d escapes u
def unsat(subset): return dpll(base + neg + [c for s in subset for c in inst(s)], {}) is None
assert unsat(S)
keep = list(S)
for s in list(S):
    trial = [t for t in keep if t is not s]
    if unsat(trial): keep = trial
def show(cl): return " or ".join(("" if val else "not ") + "_".join(map(str, names[i])) for i, val in cl)
print(len(keep), "schemas suffice:"); [print("  ", show(s)) for s in keep]
pickle.dump(keep, open("k3_keep.pkl", "wb"))
