"""
Sequential procedure: voter 1 vetoes one of a,b,c; voter 2 sees the veto and picks one of the
remaining two. Normal form: voter 1 has 3 strategies, voter 2 has 2^3 = 8 plans.
(a) Rational diagonal with Nash-style rationality (best reply in the normal form).
(b) With sequential rationality (voter 2 picks its preferred remaining alternative at EVERY veto,
    on or off the path), can voter 1 always compute a correct move? (backward induction)
"""
from itertools import product, permutations
O = "abc"; PREFS = list(permutations(O)); u = lambda p, x: 2 - p.index(x)
vetoes = list(O)
plans = list(product((0, 1), repeat=3))   # for each veto, index into remaining alternatives
def outcome(v, plan):
    rem = [x for x in O if x != v]; return rem[plan[O.index(v)]]
def br1(plan, P):
    vals = {v: u(P, outcome(v, plan)) for v in vetoes}; m = max(vals.values())
    return {v for v in vetoes if vals[v] == m}
def br2(v, Q):
    vals = {pl: u(Q, outcome(v, pl)) for pl in plans}; m = max(vals.values())
    return {pl for pl in plans if vals[pl] == m}

hits = [(P, Q) for P in PREFS for Q in PREFS
        if all(any(v not in br1(t, P) for t in br2(v, Q)) for v in vetoes)]
print(f"(a) Nash-style rational opponent: diagonal works for voter 1 in {len(hits)}/36 preference pairs")

ok = 0
for P in PREFS:
    for Q in PREFS:
        spe_plan = tuple(0 if u(Q, [x for x in O if x != v][0]) > u(Q, [x for x in O if x != v][1]) else 1
                         for v in O)
        v_star = max(vetoes, key=lambda v: u(P, outcome(v, spe_plan)))
        ok += v_star in br1(spe_plan, P)
print(f"(b) sequentially rational opponent: backward induction gives voter 1 a correct move in {ok}/36 pairs")
