"""
Exhaustive search over two-player game forms with 3 strategies each and outcomes {a,b,c}
(all three outcomes used, non-dictatorial). For each, does SOME voter i, preference P and
opponent preference Q satisfy the rational-diagonal condition?
  for every strategy s of i there is a best reply t of the opponent to s
  such that s is not a best reply of i to t.
Preferences: strict rankings of a,b,c.
"""
from itertools import product, permutations
O = "abc"; PREFS = list(permutations(O)); S = range(3)
u = lambda pref, x: 2 - pref.index(x)

def outcome(g, s1, s2): return g[3 * s1 + s2]

def dictator(g, k):
    for x in O:
        if not any(all((outcome(g, s, t) if k == 0 else outcome(g, t, s)) == x for t in S) for s in S):
            return False
    return True

def br(g, k, other_s, pref):
    vals = [u(pref, outcome(g, s, other_s) if k == 0 else outcome(g, other_s, s)) for s in S]
    m = max(vals); return {s for s in S if vals[s] == m}

def works(g):
    for i in (0, 1):
        j = 1 - i
        for P in PREFS:
            for Q in PREFS:
                if all(any(s not in br(g, i, t, P) for t in br(g, j, s, Q)) for s in S):
                    return (i, P, Q)
    return None

total = fails = 0; examples = []
for g in product(O, repeat=9):
    if set(g) != set(O) or dictator(g, 0) or dictator(g, 1):
        continue
    total += 1
    if works(g) is None:
        fails += 1
        if len(examples) < 3: examples.append(g)
print(f"non-dictatorial 3x3 game forms with 3 outcomes: {total}")
print(f"forms where the rational diagonal fails for every voter/preference: {fails}")
for g in examples:
    print("  example (rows = voter 1's strategy, cols = voter 2's):")
    for s in S: print("   ", " ".join(outcome(g, s, t) for t in S))
