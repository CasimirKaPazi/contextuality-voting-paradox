"""
Where does orientation flip on the 3-alternative surfaces?

Annulus N(U): vertices = strict comparisons x<y, triangles = strict orders.
Its two boundary rims are the two Condorcet cycles (winding +1 and -1).
Glue rim1 to rim2 by each of the 6 vertex bijections. Orient the annulus consistently
(it is orientable), then check every seam adjacency: does crossing the seam flip orientation?

Also: winding of each triple of comparisons read around a->b->c->a.
"""
from itertools import permutations
from collections import defaultdict

A = "abc"
V = [(x, y) for x in A for y in A if x != y]
def comps(o): return frozenset((o[i], o[j]) for i in range(3) for j in range(i + 1, 3))
T = [tuple(sorted(comps(o))) for o in permutations(A)]

inc = defaultdict(list)
for t in T:
    for i in range(3):
        for j in range(i + 1, 3):
            inc[frozenset((t[i], t[j]))].append(t)
boundary = {e for e, ts in inc.items() if len(ts) == 1}
adj = defaultdict(set)
for e in boundary:
    u, v = tuple(e); adj[u].add(v); adj[v].add(u)
start = next(iter(adj)); rim1 = {start}; st = [start]
while st:
    u = st.pop()
    for w in adj[u]:
        if w not in rim1: rim1.add(w); st.append(w)
rim2 = set(adj) - rim1

def winding(rel):
    """rel: set of three comparisons (x,y)='x below y'. Walk a->b->c->a, +1 for each step
    where the next alternative is above the current one, -1 otherwise; divide by 3."""
    steps = [("a", "b"), ("b", "c"), ("c", "a")]
    s = sum(1 if (u, v) in rel else -1 for (u, v) in steps)
    return s // 3 if abs(s) == 3 else 0

print("rim1", sorted(rim1), "winding", winding(set(rim1)))
print("rim2", sorted(rim2), "winding", winding(set(rim2)))
print("orders all have winding 0:", all(winding(set(t)) == 0 for t in T))

# consistent orientation of the annulus: sign per triangle relative to sorted vertex order
def directed_edges(t, s):
    p, q, w = t
    es = [(p, q), (q, w), (w, p)]
    return es if s == 1 else [(b, a) for (a, b) in es]

sign = {T[0]: 1}; st = [T[0]]
while st:
    t = st.pop()
    for e, ts in inc.items():
        if len(ts) == 2 and t in ts:
            u = ts[0] if ts[1] == t else ts[1]
            if u in sign: continue
            de = [d for d in directed_edges(t, sign[t]) if frozenset(d) == e][0]
            # neighbour must traverse e in the opposite direction
            for s in (1, -1):
                if (de[1], de[0]) in directed_edges(u, s):
                    sign[u] = s; st.append(u); break

r = lambda v: (v[1], v[0])
for img in permutations(sorted(rim2)):
    g = dict(zip(sorted(rim1), img))
    flips = 0; total = 0
    for e in boundary:
        u, v = tuple(e)
        if u in rim1 and v in rim1:
            t1 = inc[e][0]
            e2 = frozenset((g[u], g[v])); t2 = inc[e2][0]
            d1 = [d for d in directed_edges(t1, sign[t1]) if frozenset(d) == e][0]
            d1_mapped = (g[d1[0]], g[d1[1]])
            d2 = [d for d in directed_edges(t2, sign[t2]) if frozenset(d) == e2][0]
            total += 1
            if d1_mapped == d2:   # same direction across the identification = orientation flips
                flips += 1
    kind = "Klein bottle" if flips == total else ("torus" if flips == 0 else "mixed")
    tag = "  (global reversal)" if all(g[v] == r(v) for v in rim1) else ""
    print(f"gluing {dict((f'{a}<{b}', f'{c}<{d}') for (a,b),(c,d) in g.items())}: "
          f"orientation flips at {flips}/{total} seam edges -> {kind}{tag}")
