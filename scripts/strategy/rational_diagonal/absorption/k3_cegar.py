"""Find a small set of short implications between the predicates of k3_feat.py that hold on all
three-outcome stopping games (up to 7 nodes) and together imply the open lemma:
  not F_j(a)  =>  some good configuration works
(good: j with top a or b; the other player d with x not on top of its Q).
Labels: x = 0, a = 1, b = 2 (games are relabelled accordingly)."""
import pickle, itertools, sys
from sg import matrix
from k3_feat import feats
X, A, B = 0, 1, 2
data = pickle.load(open("data_k3_N7.pkl", "rb"))
names = []
for pl in "jd":
    for u in range(3): names += [(pl, "F", u), (pl, "Esc", u)]
    for m, t in itertools.permutations(range(3), 2):
        names += [(pl, "Rch", m, t), (pl, "RchA", m, t), (pl, "EscT", m, t)]
idx = {n: v for v, n in enumerate(names)}; NV = len(names)
def vec(fj, fd):
    return tuple(int(fj[n[1:]] if n[0] == "j" else fd[n[1:]]) for n in names)
V = set()
for p, o, z, W in data:
    if len(set(o) | {z}) != 3: continue
    for j in (0, 1):
        Mj, Md = matrix(p, o, z, j), matrix(p, o, z, 1 - j)
        for perm in itertools.permutations(range(3)):   # perm maps game outcome -> label
            rj = [[perm[v] for v in r] for r in Mj]; rd = [[perm[v] for v in r] for r in Md]
            fj, fd = feats(rj), feats(rd)
            if fj["F", A]: continue
            V.add(vec(fj, fd))
print(len(V), "realised predicate vectors", flush=True)
def lit(n, val=True): return (idx[n], val)
def rev(pl, t, m, w): return [[lit((pl, "F", t), False)], [lit((pl, "Esc", w))], [lit((pl, "Rch", m, t))]]
def rot(pl, t, m, w): return [[lit((pl, "F", t), False)], [lit((pl, "RchA", m, t))], [lit((pl, "EscT", w, t))]]
goods = []
for t, m, w in itertools.permutations(range(3)):
    if t != X: goods += [rev("j", t, m, w), rot("j", t, m, w)]
    if w != X: goods.append(rev("d", t, m, w))       # Q = (w, m, t): x not on top
    if m != X: goods.append(rot("d", t, m, w))       # Q = (m, w, t)
def holds(cnf, v): return all(any(v[i] == val for i, val in cl) for cl in cnf)
assert all(any(holds(g, v) for g in goods) for v in V)
# base constraints: a not forced by j; neither player forces everything
base = [[lit(("j", "F", A), False)],
        [lit(("j", "F", u), False) for u in range(3)], [lit(("d", "F", u), False) for u in range(3)]]
# negated lemma: every good fails; each good is a conjunction of literals -> clause of negations
neg = [[(i, not val) for cl in g for i, val in cl] for g in goods]
def dpll(clauses, assign):
    while True:
        changed = False
        for cl in clauses:
            un = []; sat = False
            for i, val in cl:
                if i in assign:
                    if assign[i] == val: sat = True; break
                else: un.append((i, val))
            if sat: continue
            if not un: return None
            if len(un) == 1: assign[un[0][0]] = un[0][1]; changed = True
        if not changed: break
    free = [i for i in range(NV) if i not in assign]
    if not free: return assign
    i = free[0]
    for val in (True, False):
        a2 = dict(assign); a2[i] = val; r = dpll(clauses, a2)
        if r is not None: return r
    return None
lits = [(i, val) for i in range(NV) for val in (True, False)]
def valid_on_V(cl): return all(any(v[i] == val for i, val in cl) for v in V)
learned = []
for it in range(500):
    sol = dpll(base + neg + learned, {})
    if sol is None: print("UNSAT after", len(learned), "learned clauses"); break
    s = tuple(int(sol.get(i, False)) for i in range(NV))
    found = None
    for size in (1, 2, 3):
        for cl in itertools.combinations([(i, 1 - s[i] == 1) for i in range(NV)], size):
            cl = [(i, bool(val)) for i, val in cl]
            if valid_on_V(cl): found = cl; break
        if found: break
    if not found: print("no short clause excludes", s); break
    learned.append(found)
def show(cl): return " or ".join(("" if val else "not ") + "_".join(map(str, names[i])) for i, val in cl)
for cl in learned: print("  ", show(cl))
pickle.dump((names, learned), open("k3_learned.pkl", "wb"))
