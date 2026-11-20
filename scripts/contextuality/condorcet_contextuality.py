"""
Is the Condorcet majority relation a valid (no-signalling) possibilistic empirical model
in the Abramsky-Brandenburger sense, and if so, is it contextual?

Encoding: measurements = alternatives, outcomes = a value set O carrying a strict relation
"over(x, y)" (x is placed above y). Contexts = the pairs of alternatives the majority
relation decides. The support on context {u, v} with majority u > v is a subset of
{(x, y) in O^2 : over(x, y)}.

A possibilistic model must be compatible: the marginal of each alternative is the same set
in every context containing it. The union of compatible models is compatible, so there is a
greatest compatible sub-model; we compute it by pruning (arc consistency). If it is empty,
no valid model with these supports exists at all.

Then: a global section is an assignment alternatives -> O satisfying every context.
Strong contextuality = valid model with no global section.
"""
from itertools import product

def greatest_compatible(alts, edges, O, over):
    """edges: list of (u, v) meaning majority u over v. Returns supports or None if empty."""
    S = {e: {(x, y) for x in O for y in O if over(x, y)} for e in edges}
    changed = True
    while changed:
        changed = False
        # marginal of each alternative = intersection over contexts containing it
        marg = {}
        for a in alts:
            sets = []
            for (u, v), sup in S.items():
                if a == u: sets.append({x for x, _ in sup})
                if a == v: sets.append({y for _, y in sup})
            marg[a] = set.intersection(*sets) if sets else set(O)
        for (u, v) in edges:
            new = {(x, y) for (x, y) in S[(u, v)] if x in marg[u] and y in marg[v]}
            if new != S[(u, v)]:
                S[(u, v)] = new; changed = True
        if any(len(s) == 0 for s in S.values()):
            return None
    return S

def global_sections(alts, edges, S, O, limit=5):
    out = []
    for vals in product(O, repeat=len(alts)):
        g = dict(zip(alts, vals))
        if all((g[u], g[v]) in S[(u, v)] for (u, v) in edges):
            out.append(g)
            if len(out) >= limit: break
    return out

def report(name, alts, edges, O, over):
    S = greatest_compatible(alts, edges, O, over)
    if S is None:
        print(f"{name:55s} -> no valid (no-signalling) model exists")
        return None
    gs = global_sections(alts, edges, S, O, limit=1)
    print(f"{name:55s} -> valid model; global section: {gs[0] if gs else 'NONE (strongly contextual)'}")
    return S, gs

cond3 = (list("abc"), [("a", "b"), ("b", "c"), ("c", "a")])          # Condorcet cycle
trans3 = (list("abc"), [("a", "b"), ("b", "c"), ("a", "c")])         # transitive majority
cond4 = (list("abcd"), [("a", "b"), ("b", "c"), ("c", "d"), ("d", "a")])  # total 4-cycle

print("== Finite LINE: O = {0..k-1}, over(x,y) = x > y ==")
for k in (3, 5, 10, 40):
    O = range(k); over = lambda x, y: x > y
    report(f"Condorcet 3-cycle, k={k}", *cond3, O, over)
    report(f"Transitive majority, k={k}", *trans3, O, over)
    report(f"Total 4-cycle, k={k}", *cond4, O, over)

print("\n== Finite CIRCLE: O = Z_m, over(x,y) = (x - y) mod m in 1..floor((m-1)/2) ==")
def circle(m):
    h = (m - 1) // 2
    return range(m), (lambda x, y: 1 <= (x - y) % m <= h)
for m in (5, 7, 12):
    O, over = circle(m)
    r = report(f"Condorcet 3-cycle, m={m}", *cond3, O, over)
    if r and r[1]:
        g = r[1][0]
        d = [((g[u] - g[v]) % m) for (u, v) in cond3[1]]   # lifted differences, each in (0, m/2)
        print(f"{'':57s}lifted differences {d}, sum = {sum(d)} = {sum(d)//m} x m  -> winding {sum(d)//m}")
    r = report(f"Transitive majority, m={m}", *trans3, O, over)
    if r and r[1]:
        g = r[1][0]
        # winding around the triangle a->b->c->a: differences a-b, b-c, c-a lifted to (-m/2, m/2)
        lift = lambda z: ((z + m // 2) % m) - m // 2
        d = [lift(g["a"] - g["b"]), lift(g["b"] - g["c"]), lift(g["c"] - g["a"])]
        print(f"{'':57s}lifted differences {d}, sum = {sum(d)} -> winding {sum(d)//m}")

print("\n== Unbounded LINE (Z), truncated window: is the marginal ever forced to shrink? ==")
# On Z the full supports {x > y} have marginal Z for every alternative, so the model is
# compatible; but no global section exists since x_a > x_b > x_c > x_a is impossible.
# Check numerically that pruning only eats the window's edges (finite artefact):
for k in (10, 40):
    O = range(k); over = lambda x, y: x > y
    S = {e: {(x, y) for x in O for y in O if over(x, y)} for e in cond3[1]}
    margs = {a: sorted(set.intersection(*[{p[i] for p in S[e]} for e in cond3[1]
             for i in (0, 1) if e[i] == a])) for a in cond3[0]}
    print(f"k={k}: before pruning, marginal of a = [{margs['a'][0]}..{margs['a'][-1]}] (size {len(margs['a'])}) "
          f"-- the first pruning round removes one value at each end, and pruning never stops")

print("\n== Zeng-Zahn encoding: alternatives as measurements, outcome 'chosen'(1)/'not'(0), contexts = menus ==")
def zz(menus_choice):
    alts = sorted({x for m in menus_choice for x in m})
    sec = []
    for vals in product((0, 1), repeat=len(alts)):
        s = dict(zip(alts, vals))
        if all({x for x in m if s[x] == 1} == ch for m, ch in menus_choice.items()):
            sec.append(s)
    signalling = any(
        (x in c1) != (x in c2)
        for m1, c1 in menus_choice.items() for m2, c2 in menus_choice.items()
        for x in set(m1) & set(m2))
    return sec, signalling
for name, mc in [
    ("Condorcet: {ab}->a, {bc}->b, {ca}->c", {("a", "b"): {"a"}, ("b", "c"): {"b"}, ("a", "c"): {"c"}}),
    ("Transitive a>b>c: {ab}->a, {bc}->b, {ac}->a", {("a", "b"): {"a"}, ("b", "c"): {"b"}, ("a", "c"): {"a"}}),
]:
    sec, sig = zz(mc)
    print(f"{name:50s} global sections: {len(sec)}  signalling: {sig}")
