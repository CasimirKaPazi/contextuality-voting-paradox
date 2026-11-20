"""
Does the diagonal survive when the opposing programs must be RATIONAL voters?

Condition for voter i with preference P, others with fixed preferences Q:
  for every ballot b of i there is a profile c of the others' ballots such that
   (1) every other voter k is best-responding in (b, c) under Q_k, and
   (2) b is NOT a best reply for i against c under P.
If this holds, the opponents can run "simulate i's program -> b -> play c(b)":
each opponent is rational in the actual play, and i's program is wrong.

Rules (ballots = strict rankings of 3 alternatives, lexicographic tie-breaking a<b<c):
plurality, Borda, instant runoff (IRV), Black (Condorcet winner, else Borda).
"""
from itertools import permutations, product

ALTS = "abc"
RANKS = list(permutations(ALTS))          # ballots and preferences alike
TB = {x: i for i, x in enumerate(ALTS)}    # tie-break: earlier letter wins

def argmax_tb(score):
    return min(ALTS, key=lambda x: (-score[x], TB[x]))

def plurality(prof):
    s = {x: 0 for x in ALTS}
    for r in prof: s[r[0]] += 1
    return argmax_tb(s)

def borda(prof):
    s = {x: 0 for x in ALTS}
    for r in prof:
        for pos, x in enumerate(r): s[x] += 2 - pos
    return argmax_tb(s)

def irv(prof):
    alive = list(ALTS)
    while len(alive) > 1:
        s = {x: 0 for x in alive}
        for r in prof:
            top = next(x for x in r if x in alive); s[top] += 1
        # eliminate fewest first-preferences; tie: eliminate the LATER letter
        loser = max(alive, key=lambda x: (-s[x], TB[x]))
        alive.remove(loser)
    return alive[0]

def black(prof):
    n = len(prof)
    for x in ALTS:
        if all(sum(r.index(x) < r.index(y) for r in prof) * 2 > n for y in ALTS if y != x):
            return x
    return borda(prof)

RULES = {"plurality": plurality, "Borda": borda, "IRV": irv, "Black": black}

def util(pref, x): return 2 - pref.index(x)

def best_replies(rule, prof, k, pref):
    vals = {}
    for alt_ballot in RANKS:
        p = list(prof); p[k] = alt_ballot
        vals[alt_ballot] = util(pref, rule(p))
    m = max(vals.values())
    return {bb for bb, v in vals.items() if v == m}

def check(rule, n, i=0):
    hits = []
    others = [k for k in range(n) if k != i]
    for P in RANKS:
        for Q in product(RANKS, repeat=n - 1):
            prefs = {k: q for k, q in zip(others, Q)}
            ok_all_b = True
            for b in RANKS:
                found = False
                for c in product(RANKS, repeat=n - 1):
                    prof = [None] * n; prof[i] = b
                    for k, ck in zip(others, c): prof[k] = ck
                    if not all(prof[k] in best_replies(rule, prof, k, prefs[k]) for k in others):
                        continue            # (1) some opponent not best-responding
                    if b in best_replies(rule, prof, i, P):
                        continue            # (2) b is a best reply here -> no refutation
                    found = True; break
                if not found:
                    ok_all_b = False; break
            if ok_all_b:
                hits.append((P, Q))
    return hits

if __name__ == "__main__":
    for n in (2, 3):
        for name, rule in RULES.items():
            hits = check(rule, n)
            total = len(RANKS) ** n
            ex = hits[0] if hits else None
            exs = (f"e.g. P={''.join(ex[0])}, others={[''.join(q) for q in ex[1]]}" if ex else "")
            print(f"n={n} {name:9s}: rational diagonal works for {len(hits):3d}/{total} preference profiles  {exs}")
