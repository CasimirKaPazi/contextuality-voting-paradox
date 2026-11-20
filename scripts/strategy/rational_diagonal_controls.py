"""Control cases for rational_diagonal.py (dictatorial and two-outcome rules must give no cases),
and a worked example under Borda with two voters."""
from rational_diagonal import check, RANKS, best_replies, util, borda
from itertools import product

controls = {
  "dictator = voter i":        lambda p: p[0][0],
  "dictator = other voter":    lambda p: p[1][0],
  "two outcomes (a vs b maj.)": lambda p: "a" if sum(r.index("a") < r.index("b") for r in p) * 2 >= len(p) else "b",
}
for n in (2, 3):
    for name, rule in controls.items():
        print(f"control n={n} {name:28s}: {len(check(rule, n))} hits (expected 0)")

# full example: n=2 Borda, P=abc for voter i, other voter prefers bca
P = tuple("abc"); Q = tuple("bca")
print("\nExample: Borda, n=2, voter i prefers abc, opponent prefers bca")
for b in RANKS:
    for c in RANKS:
        prof = [b, c]
        if c in best_replies(borda, prof, 1, Q) and b not in best_replies(borda, prof, 0, P):
            better = sorted(best_replies(borda, prof, 0, P))[0]
            print(f"  i casts {''.join(b)} -> opponent best-responds with {''.join(c)} -> outcome {borda(prof)};"
                  f" i would have done better with {''.join(better)} (outcome {borda([better, c])})")
            break
