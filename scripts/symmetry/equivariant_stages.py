"""Equivariant obstruction theory for three alternatives: the stages, one at a time
(working note *Equivariant Obstructions*).

Profiles of n voters form the cube complex X = Y^n, where Y is the hexagon of the six rankings
(adjacent rankings differ in one comparison). The voters' permutations S_n act on X only; the
renamings of the alternatives and reversal (together the dihedral group D_6 of the hexagon) act on
X and on Y. A rule is local if one voter's step moves the social ranking by at most one step, and
Pareto if it respects every comparison on which all voters agree. Every rule satisfying independence
of irrelevant alternatives is local; every unanimous IIA rule into rankings is Pareto.

Part 1, stage 0 (vertices). An equivariant rule sends a profile into the rankings fixed by its
        stabiliser. For anonymous profiles and the symmetry groups N (renamings), R (reversal) and
        N + R, lists the n at which some profile has no fixed ranking: N and N + R fail exactly when
        gcd(n, 6) > 1, R exactly when n is even. For single winners and N it reproduces Moulin's
        condition for m = 3 (failure exactly when 3 divides n).
Part 2, stage 1 (edge midpoints). After subdividing, the midpoint of a step is the profile in which
        the moving voter is indifferent on the flipped pair. Its stabiliser never empties the fixed set
        of the subdivided hexagon (no stage-1 obstruction), but with neutrality some stabilisers swap the
        two ends of the step; there the rule must flip the social comparison of that pair: the moving
        voter is pivotal. For one voter every step is of this kind, so a neutral local rule of one
        voter has degree +1 or -1. Counts the forced pivots.
Part 3, stage 2 (the degree). Decides by 0/1 programs whether a local Pareto rule exists that treats
        the voters of each block alike. Predicted by the note: the cohomological obstruction is the
        class of 1 in Z/g, g the gcd of the block sizes, but Pareto pins the degrees to 0 or 1, so a
        rule exists exactly when some block has size 1. Anonymous rules (one block of size 2 to 5) and
        blocks (2, 2), (3, 3) fail as the torsion class predicts; blocks (2, 3) fail although g = 1,
        by the pinning. Rigidity is a further layer: every local Pareto rule of two voters is a
        dictatorship, while for three voters there is one with degrees (0, 0, 1) that is not.
Run: python3 equivariant_stages.py   (numpy and scipy; about twenty seconds)
"""
import itertools
import math
from itertools import combinations_with_replacement, permutations

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix

HEX = [(0, 1, 2), (1, 0, 2), (1, 2, 0), (2, 1, 0), (2, 0, 1), (0, 2, 1)]  # cyclic order of rankings
POS = {r: k for k, r in enumerate(HEX)}
PAIRS = [(0, 1), (1, 2), (0, 2)]


def above(r, x, y):
    return r.index(x) < r.index(y)


def adjacent(r, s):
    return (POS[r] - POS[s]) % 6 in (1, 5)


def step(a, b):
    return {0: 0, 1: 1, 5: -1}.get((POS[b] - POS[a]) % 6)


# ---------------------------------------------------------------- the group D_6 on rankings
def make_elem(pi, rev):
    def act(r):
        s = tuple(pi[x] for x in r)
        return s[::-1] if rev else s
    act.name = ("rev o " if rev else "") + "".join("abc"[pi[x]] for x in range(3))
    act.renaming = pi
    act.rev = rev
    return act


ELEMS = [make_elem(pi, rev) for pi in permutations(range(3)) for rev in (0, 1)]
IDENTITY = (0, 1, 2)
GROUPS = {
    "N": [g for g in ELEMS if not g.rev],
    "R": [g for g in ELEMS if g.renaming == IDENTITY],
    "N+R": ELEMS,
}


def ms(profile):
    return tuple(sorted(profile, key=POS.get))


def multisets(n):
    return list(combinations_with_replacement(HEX, n))


def stabiliser(M, group):
    return [g for g in group if ms(g(r) for r in M) == M]


def fixed_rankings(H):
    return [r for r in HEX if all(g(r) == r for g in H)]


def fixed_winners(H):
    return [x for x in range(3) if all(g.renaming[x] == x for g in H)]


def part1(nmax=10):
    print("Part 1: stage 0, fixed outputs at anonymous profiles")
    for name in ("N", "R", "N+R"):
        fails = []
        for n in range(1, nmax + 1):
            bad = [M for M in multisets(n) if not fixed_rankings(stabiliser(M, GROUPS[name]))]
            if bad:
                fails.append(n)
        expect = [n for n in range(1, nmax + 1)
                  if (math.gcd(n, 6) > 1 if name != "R" else n % 2 == 0)]
        print(f"  rankings, anonymity + {name:3}: stage 0 fails for n in {fails}"
              f"  {'(as predicted)' if fails == expect else 'MISMATCH ' + str(expect)}")
    fails = [n for n in range(1, nmax + 1)
             if any(not fixed_winners(stabiliser(M, GROUPS['N'])) for M in multisets(n))]
    print(f"  single winners, anonymity + N: stage 0 fails for n in {fails}"
          f"  {'(Moulin: 3 divides n)' if fails == [n for n in range(1, nmax + 1) if n % 3 == 0] else 'MISMATCH'}")
    # Without anonymity a stabiliser fixes every ballot of the profile, so it fixes a ranking.
    for name, group in GROUPS.items():
        ok = all(fixed_rankings([g for g in group if all(g(r) == r for r in prof)])
                 for n in range(1, 4) for prof in itertools.product(HEX, repeat=n))
        assert ok
    print("  without anonymity stage 0 never fails (checked for n <= 3 and all three groups)")
    print()


# ---------------------------------------------------------------- stage 1: edge midpoints
# Subdivided hexagon: vertices ('v', r) and midpoints ('m', frozenset{r, r'}) of edges.
def fixed_subdivided(H):
    pts = [("v", r) for r in HEX if all(g(r) == r for g in H)]
    for k in range(6):
        e = frozenset({HEX[k], HEX[(k + 1) % 6]})
        if all(frozenset(g(r) for r in e) == e for g in H):
            pts.append(("m", e))
    return pts


def part2(nmax=7):
    print("Part 2: stage 1, edge midpoints (a voter indifferent on the flipped pair)")
    for name in ("N", "R", "N+R"):
        group = GROUPS[name]
        row = []
        for n in range(1, nmax + 1):
            edges = forced = empty = 0
            for M in multisets(n - 1):
                for r in HEX:
                    for r2 in HEX:
                        if not adjacent(r, r2) or r > r2:
                            continue
                        edges += 1
                        H = [g for g in group if ms(g(x) for x in M) == M and {g(r), g(r2)} == {r, r2}]
                        if not fixed_subdivided(H):
                            empty += 1
                        if any(g(r) == r2 for g in H):
                            forced += 1
            row.append(f"n={n}: {forced}/{edges}" + (f" EMPTY {empty}" if empty else ""))
        print(f"  anonymity + {name:3}: forced pivots / steps   " + ", ".join(row))
    # one voter, neutrality only: every step is forced, so the degree is +-1
    print("  one voter with neutrality: every step forces a pivot, and outcomes two steps apart differ")
    print("  (a 3-cycle maps one ranking to the other and fixes no ranking), so the walk is monotone")
    print("  and the degree is +1 or -1")
    local = []
    for s0 in HEX:  # a neutral rule of one voter is fixed by its value at abc: F(pi abc) = pi s0
        F = {g(HEX[0]): g(s0) for g in GROUPS["N"]}
        if all(step(F[r], F[HEX[(POS[r] + 1) % 6]]) is not None for r in HEX):
            local.append((s0, sum(step(F[HEX[k]], F[HEX[(k + 1) % 6]]) for k in range(6)) // 6))
    print(f"  the neutral local rules of one voter, by their value at abc, with degrees: {local}")
    print()


# ---------------------------------------------------------------- stage 2: local Pareto rules with block symmetry
def pareto_domain(rankings):
    dom = []
    for s in HEX:
        if all(above(s, x, y) == above(rankings[0], x, y)
               for x, y in PAIRS if len({above(r, x, y) for r in rankings}) == 1):
            dom.append(s)
    return dom


def block_vertices(blocks):
    per = [multisets(k) for k in blocks]
    return list(itertools.product(*per))


def neighbours(v):
    """One voter's step: replace one copy of a ranking in one block by an adjacent ranking."""
    out = set()
    for j, M in enumerate(v):
        for i, r in enumerate(M):
            for r2 in HEX:
                if adjacent(r, r2):
                    M2 = ms(M[:i] + (r2,) + M[i + 1:])
                    out.add(v[:j] + (M2,) + v[j + 1:])
    return out


def local_pareto_system(blocks):
    """0/1 program: x[v, s] = 1 if the rule gives ranking s at vertex v; one ranking per vertex,
    only Pareto-admissible rankings, and at every step of one voter the social ranking moves by
    at most one position on the hexagon."""
    verts = block_vertices(blocks)
    idx = {v: k for k, v in enumerate(verts)}
    V = len(verts)
    rows, cols, vals, lo, hi = [], [], [], [], []
    ub = np.zeros(6 * V)
    r = 0
    for k, v in enumerate(verts):
        for s in pareto_domain([x for M in v for x in M]):
            ub[6 * k + POS[s]] = 1
        for s in range(6):
            rows.append(r); cols.append(6 * k + s); vals.append(1)
        lo.append(1); hi.append(1); r += 1
    for k, v in enumerate(verts):
        for w in neighbours(v):
            j = idx[w]
            for s in range(6):
                rows.append(r); cols.append(6 * k + s); vals.append(1)
                for t in (s - 1, s, s + 1):
                    rows.append(r); cols.append(6 * j + t % 6); vals.append(-1)
                lo.append(-np.inf); hi.append(0); r += 1
    A = coo_matrix((vals, (rows, cols)), shape=(r, 6 * V)).tocsr()
    return verts, idx, A, lo, hi, ub


def solve(blocks, c=None, fix=None):
    verts, idx, A, lo, hi, ub = local_pareto_system(blocks)
    ub = ub.copy()
    if fix:
        for v, s in fix.items():
            for t in range(6):
                if t != POS[s]:
                    ub[6 * idx[v] + t] = 0
    res = milp(np.zeros(len(ub)) if c is None else c(verts), constraints=LinearConstraint(A, lo, hi),
               integrality=np.ones(len(ub)), bounds=Bounds(0, ub))
    if res.status != 0:
        return None, res
    x = res.x.round().astype(int).reshape(len(verts), 6)
    return {v: HEX[int(np.argmax(x[k]))] for k, v in enumerate(verts)}, res


def degrees(rule, blocks):
    """Winding of the social ranking while one voter of block j walks once around the hexagon,
    at the context where every other voter holds abc."""
    out = []
    for j, k in enumerate(blocks):
        base = [tuple([HEX[0]] * kk) for kk in blocks]
        walk = []
        for t in range(7):
            v = list(base)
            v[j] = ms((HEX[t % 6],) + tuple([HEX[0]] * (k - 1)))
            walk.append(rule[tuple(v)])
        out.append(sum(step(a, b) for a, b in zip(walk, walk[1:])) // 6)
    return out


def part3():
    print("Part 3: stage 2, local Pareto rules symmetric within blocks of voters (0/1 programs)")
    for blocks in [(1,), (2,), (3,), (4,), (5,), (1, 1), (2, 1), (3, 1), (1, 1, 1), (2, 2), (2, 3), (3, 3)]:
        g = math.gcd(*blocks)
        rule, _ = solve(blocks)
        if rule is None:
            res = "none exists"
        else:
            d = degrees(rule, blocks)
            res = f"exists; degree per block {d}"
        pred = "exists" if 1 in blocks else "none"
        print(f"  blocks {str(blocks):9} Z/{g} obstruction {'vanishes' if g == 1 else 'nonzero '};"
              f" a block of size 1: {'yes' if 1 in blocks else 'no '} -> {res}"
              f"  {'(as predicted)' if res.startswith(pred[:4]) else 'MISMATCH'}")
    # Rigidity is a further layer. Two voters: the output is always one of the two ballots, and once
    # it follows voter 2 at (abc, cba) it follows voter 2 everywhere, so every rule is a dictatorship.
    def off_both(verts):
        vec = np.zeros(6 * len(verts))
        for k, v in enumerate(verts):
            for t in range(6):
                if HEX[t] not in (v[0][0], v[1][0]):
                    vec[6 * k + t] = -1
        return vec
    rule, res = solve((1, 1), c=off_both)
    print(f"  2 voters: most profiles at which the output is neither ballot: {int(round(-res.fun))}")
    # From three voters on, local Pareto rules need not be dictatorships.
    for n in (2, 3):
        blocks = (1,) * n
        # voter 1 holds abc, the middle voters bac, the last voter cba; the rule must follow the last
        pivot = ((HEX[0],),) + ((HEX[1],),) * (n - 2) + ((HEX[3],),)

        def c(verts):
            vec = np.zeros(6 * len(verts))
            for k, v in enumerate(verts):
                if v[0][0] != v[-1][0]:
                    vec[6 * k + POS[v[0][0]]] = -1
            return vec
        rule, res = solve(blocks, c=c, fix={pivot: pivot[-1][0]})
        agree = [sum(rule[v] == v[i][0] for v in rule) for i in range(n)]
        print(f"  {n} voters: a local Pareto rule with degrees {degrees(rule, blocks)} agrees with the voters'"
              f" ballots at {agree} of {len(rule)} profiles"
              + ("  (a dictatorship)" if max(agree) == len(rule) else "  (not a dictatorship)"))
    print()


if __name__ == "__main__":
    part1()
    part2()
    part3()
