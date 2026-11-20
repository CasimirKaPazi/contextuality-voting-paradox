"""
Baryshnikov / Livson-Pritam-Prokopenko model for 3 alternatives.
Vertices: strict pairwise comparisons x<y (6 of them).
Triangles: strict orders (each contains 3 comparisons) -> annulus.
Boundary rims: the two Condorcet cycles.
We glue rim1 -> rim2 by each of the 6 vertex bijections and test orientability.
We also check which bijection is the restriction of global reversal r(x<y) = (y<x),
and whether r is a free, orientation-reversing involution of the annulus.
"""
from itertools import permutations
from collections import defaultdict

A = "abc"
V = [(x, y) for x in A for y in A if x != y]           # (x,y) means x<y
orders = list(permutations(A))
def comps(o):
    return frozenset((o[i], o[j]) for i in range(3) for j in range(i + 1, 3))
T = [tuple(sorted(comps(o))) for o in orders]           # triangles as vertex triples

# edges and their incidence
inc = defaultdict(list)
for t in T:
    for i in range(3):
        for j in range(i + 1, 3):
            inc[frozenset((t[i], t[j]))].append(t)
boundary = [e for e, ts in inc.items() if len(ts) == 1]
rimverts = set(v for e in boundary for v in e)
# split boundary into two rims (connected components)
adj = defaultdict(set)
for e in boundary:
    u, v = tuple(e); adj[u].add(v); adj[v].add(u)
def comp(s):
    seen, st = {s}, [s]
    while st:
        u = st.pop()
        for w in adj[u]:
            if w not in seen: seen.add(w); st.append(w)
    return seen
rim1 = comp(next(iter(rimverts))); rim2 = rimverts - rim1
print("rim1:", sorted(rim1)); print("rim2:", sorted(rim2))
chi = len(V) - len(inc) + len(T)
print("annulus check: V,E,F =", len(V), len(inc), len(T), "chi =", chi)

r = lambda v: (v[1], v[0])

def orientable(glue):
    """glue: dict rim1-vertex -> rim2-vertex. Edge classes: interior edges as-is,
    rim1 edge (u,v) identified with rim2 edge (glue u, glue v) preserving direction."""
    def canon(u, v):
        # returns (edge-class key, sign) for directed edge u->v
        if u in rim1 and v in rim1 and frozenset((u, v)) in boundary:
            u, v = glue[u], glue[v]
        key = tuple(sorted((u, v)))
        return key, (1 if (u, v) == key else -1)
    # orientation unknowns per triangle: s_t in {+1,-1}; triangle t=(p,q,w) has directed edges p->q, q->w, w->p
    uses = defaultdict(list)
    for t in T:
        p, q, w = t
        for (u, v) in ((p, q), (q, w), (w, p)):
            k, s = canon(u, v); uses[k].append((t, s))
    # each edge class must be used exactly twice (closed surface) with opposite induced directions
    for k, lst in uses.items():
        if len(lst) != 2: return None
    sign = {T[0]: 1}; st = [T[0]]
    nbrs = defaultdict(list)
    for k, ((t1, s1), (t2, s2)) in uses.items():
        nbrs[t1].append((t2, s1, s2)); nbrs[t2].append((t1, s2, s1))
    ok = True
    while st:
        t = st.pop()
        for (u, s_t, s_u) in nbrs[t]:
            need = -sign[t] * s_t * s_u      # want sign[t]*s_t + sign[u]*s_u == 0
            if u in sign:
                if sign[u] != need: ok = False
            else:
                sign[u] = need; st.append(u)
    return ok

for img in permutations(sorted(rim2)):
    glue = dict(zip(sorted(rim1), img))
    res = orientable(glue)
    is_r = all(glue[v] == r(v) for v in rim1)
    name = {True: "torus", False: "KLEIN BOTTLE", None: "not a closed surface"}[res]
    print(dict((f"{a}<{b}", f"{c}<{d}") for (a, b), (c, d) in glue.items()),
          "->", name, "  <== global reversal r" if is_r else "")

# Is r orientation-reversing on the annulus? r maps triangles to triangles;
# compare induced orientations using a consistent orientation of the annulus.
def annulus_orientation():
    uses = defaultdict(list)
    for t in T:
        p, q, w = t
        for (u, v) in ((p, q), (q, w), (w, p)):
            k = tuple(sorted((u, v))); uses[k].append((t, 1 if (u, v) == k else -1))
    sign = {T[0]: 1}; st = [T[0]]
    while st:
        t = st.pop()
        for k, lst in uses.items():
            if len(lst) == 2 and any(x[0] == t for x in lst):
                (t1, s1), (t2, s2) = lst
                if t2 == t: (t1, s1), (t2, s2) = (t2, s2), (t1, s1)
                need = -sign[t] * s1 * s2
                if t2 not in sign: sign[t2] = need; st.append(t2)
    return sign
sgn = annulus_orientation()
def perm_parity(a, b):
    # parity of permutation taking tuple a to tuple b
    p = [a.index(x) for x in b]; par = 1
    for i in range(3):
        for j in range(i + 1, 3):
            if p[i] > p[j]: par = -par
    return par
rev = []
for t in T:
    img = tuple(r(v) for v in t); timg = tuple(sorted(img))
    rev.append(sgn[t] * sgn[timg] * perm_parity(timg, img))
print("r fixes a vertex?", any(r(v) == v for v in V), "| r swaps rims?", set(map(r, rim1)) == rim2)
print("r orientation behaviour per triangle (-1 = reversing):", rev)
