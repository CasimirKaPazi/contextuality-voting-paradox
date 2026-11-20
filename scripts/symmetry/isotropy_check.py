"""Isotropy check: where the symmetry goes, profile by profile.

An anonymous profile is a multiset of strict rankings. The renamings of the
alternatives (the symmetric group S_m) act on profiles and on outputs. Its
stabiliser H is the group of renamings that map the profile to itself.

Lemma (isotropy). An anonymous and neutral rule must send a profile with
stabiliser H to an output fixed by every element of H. Conversely, on a finite
set of profiles, such a rule exists as soon as every profile has an H-fixed
admissible output: choose one representative per orbit, choose a fixed output
for it, and transport it along the orbit.

So existence of anonymous, neutral rules with a given kind of output is
decided by the fixed-point sets of stabilisers. This script computes, for
small m and n, whether every profile has a fixed admissible output, for:

  winner      a single alternative                     (compare Moulin 1991)
  winner+P    a single Pareto-optimal alternative      (compare gcd(n, m!) = 1)
  ranking     a strict ranking                          (compare gcd(n, m!) = 1)
  weak order  a weak order                              (always: full indifference)
  lottery     a lottery over alternatives               (always: average of an orbit)

and compares with the arithmetic conditions from the literature.
"""
from itertools import permutations, combinations_with_replacement
from math import gcd, factorial
import sys


def divisor_sum_representable(m, n):
    """Can m be written as a sum of divisors of n that exceed 1?"""
    ds = [d for d in range(2, n + 1) if n % d == 0]
    reach = [False] * (m + 1)
    reach[0] = True
    for s in range(1, m + 1):
        reach[s] = any(d <= s and reach[s - d] for d in ds)
    return reach[m]


def analyse(m, n):
    alts = list(range(m))
    ranks = list(permutations(alts))
    idx = {r: i for i, r in enumerate(ranks)}
    perms = list(permutations(alts))
    # action of each renaming on ranking indices
    act = [[idx[tuple(s[x] for x in r)] for r in ranks] for s in perms]
    ok = {"winner": True, "winner+P": True, "ranking": True}
    witness = {}
    for prof in combinations_with_replacement(range(len(ranks)), n):
        H = [s for s, a in zip(perms, act)
             if tuple(sorted(a[i] for i in prof)) == prof]
        if len(H) == 1:
            continue
        fixed = [x for x in alts if all(s[x] == x for s in H)]
        if not fixed and ok["winner"]:
            ok["winner"] = False
            witness["winner"] = (prof, H)
        # Pareto-optimal: not unanimously beaten by another alternative
        rk = [ranks[i] for i in prof]
        def dominated(x):
            return any(all(r.index(y) < r.index(x) for r in rk) for y in alts if y != x)
        if not [x for x in fixed if not dominated(x)] and ok["winner+P"]:
            ok["winner+P"] = False
            witness["winner+P"] = (prof, H)
        if ok["ranking"]:  # renamings act freely on rankings
            ok["ranking"] = False
            witness["ranking"] = (prof, H)
    return ok, witness, ranks


def main():
    cases = [(3, n) for n in range(2, 11)] + [(4, n) for n in range(2, 7)] + [(5, 2), (5, 3)]
    if len(sys.argv) > 1 and sys.argv[1] == "quick":
        cases = [(3, n) for n in range(2, 7)] + [(4, n) for n in range(2, 5)]
    print(" m  n | winner  Moulin | winner+P ranking gcd(n,m!)=1 | weak lottery")
    agree = True
    for m, n in cases:
        ok, wit, ranks = analyse(m, n)
        moulin = not divisor_sum_representable(m, n)
        g = gcd(n, factorial(m)) == 1
        agree &= (ok["winner"] == moulin) and (ok["winner+P"] == g) and (ok["ranking"] == g)
        print(f"{m:2d} {n:2d} | {str(ok['winner']):6s}  {str(moulin):6s} | "
              f"{str(ok['winner+P']):8s} {str(ok['ranking']):7s} {str(g):12s} | True True")
    print("all comparisons agree:", agree)
    # one case beyond enumeration: m = 5, n = 6, renaming (0 1)(2 3 4) of order 6
    s = (1, 0, 3, 4, 2)
    r = (0, 1, 2, 3, 4)
    orbit, cur = [], r
    for _ in range(6):
        orbit.append(cur)
        cur = tuple(s[x] for x in cur)
    print("m=5, n=6: orbit of one ranking under (0 1)(2 3 4) has", len(set(orbit)),
          "rankings; the profile is fixed by a renaming without a fixed alternative,",
          "so no anonymous, neutral, resolute rule exists (5 = 2 + 3, divisors of 6).")


if __name__ == "__main__":
    main()
