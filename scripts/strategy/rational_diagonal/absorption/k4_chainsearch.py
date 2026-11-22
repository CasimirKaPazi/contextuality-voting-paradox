"""Four outcomes: is there a fixed family of configurations, like the chain of three outcomes, that
always contains a working one?  Instances: stopping games with four outcomes (up to 6 nodes),
a player i not forcing a, the opponent o not forcing c; e, f the other two (both labelings).
Shapes: configurations of i with top a and of o with top c, orders labelled by a, c, e, f."""
import pickle, itertools, collections
from sg import forces
data = pickle.load(open("data_k4_N6.pkl", "rb"))
shapes = []
for rest in itertools.permutations("cef"):
    for kind in ("rev", "rot"): shapes.append(("i", kind, "a" + "".join(rest)))
for rest in itertools.permutations("aef"):
    for kind in ("rev", "rot"): shapes.append(("o", kind, "c" + "".join(rest)))
sidx = {s: n for n, s in enumerate(shapes)}
inst = collections.Counter()
for p, o, z, W in data:
    pr = set(o) | {z}
    if len(pr) != 4: continue
    F = [forces(p, o, z, 0), forces(p, o, z, 1)]
    for i in (0, 1):
        for a in pr - F[i]:
            for c in pr - F[1 - i] - {a}:
                e1, f1 = sorted(pr - {a, c})
                for e, f in ((e1, f1), (f1, e1)):
                    L = {a: "a", c: "c", e: "e", f: "f"}; mask = 0
                    for pl, P, kind in W:
                        lab = "".join(L[w] for w in P)
                        who = "i" if pl == i else "o"
                        key = (who, kind, lab)
                        if key in sidx: mask |= 1 << sidx[key]
                    inst[mask] += 1
print(len(inst), "distinct instance masks;", inst[0], "instances with no shape at all")
masks = [m for m in inst if m]
best = None
for r in range(1, 9):
    for C in itertools.combinations(range(len(shapes)), r):
        cm = sum(1 << s for s in C)
        if all(m & cm for m in masks):
            best = C; break
    if best: break
print("smallest cover:", r if best else None, [shapes[s] for s in best] if best else None)
