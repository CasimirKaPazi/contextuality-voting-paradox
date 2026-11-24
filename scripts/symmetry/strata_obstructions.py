"""Obstructions on the fixed strata, for continuous rules on the realised sphere of rankings
(working note *Equivariant Obstructions*, Section 6, Proposition 6).

Rankings of m alternatives: the unit sphere Y of the space V of utility vectors with sum zero, of
dimension m - 1; ties are allowed in ballots and outputs. Profiles X = Y^n. The symmetry is
K = P x Gamma', with P a product of symmetric groups on blocks of voters and Gamma' a group of
renamings, possibly with reversal (-1 on V). A rule is a continuous K-equivariant map X -> Y that is
the identity on unanimous profiles.

For h = (sigma, gamma) in K the fixed stratum X^h is a product over the cycles of sigma: a cycle of
length l contributes the fixed sphere of gamma^l. The rule sends X^h into Y^gamma, a sphere of
dimension k - 1 with k = dim V^gamma. Call a cycle short if V^(gamma^l) = V^gamma. The note proves:
  k = 0:  obstruction if X^h is not empty (every cycle has dim V^(gamma^l) >= 1);
  k = 1:  obstruction if there are no short cycles, or if the centraliser of gamma in Gamma' contains an
          element reversing the line V^gamma and every class of short cycles (same block, same length)
          has even size: a May condition;
  k >= 2: obstruction Z/g_h, g_h the gcd of the sizes of the classes of short cycles; if there is no
          short cycle the obstruction is not torsion (1 in Z).
The top stage is h = identity: Z/g with g the gcd of the block sizes.

The script lists, for m = 3 and 4, n <= 8 and every block structure, whether the top stage obstructs
and which strata obstruct. Rows in which the top stage vanishes but a stratum does not are marked.
Among them, for m = 4 with neutrality, is Proposition 5: blocks (2, 3), the stratum of a swap of the two
voters combined with a transposition, Z/3.
These are the primary obstructions only. For an even number of alternatives the cup square
(Proposition 5) rules out every block structure without a block of size 1, whatever the group on the
alternatives, so a row without obstructions is not an existence claim.
Run: python3 strata_obstructions.py   (numpy; a few seconds; rows are printed for n <= 3 and wherever
     the top stage vanishes but a stratum obstructs)
"""
import math
from functools import reduce
from itertools import permutations

import numpy as np


def partitions(n, maxpart=None):
    maxpart = maxpart or n
    if n == 0:
        yield ()
        return
    for k in range(min(n, maxpart), 0, -1):
        for rest in partitions(n - k, k):
            yield (k,) + rest


def cycle_type(perm):
    seen, out = set(), []
    for i in range(len(perm)):
        if i not in seen:
            c, j = 0, i
            while j not in seen:
                seen.add(j); j = perm[j]; c += 1
            out.append(c)
    return out


def matrix(pi, rev, m):
    P = np.zeros((m, m))
    for i, j in enumerate(pi):
        P[j, i] = 1
    return -P if rev else P


def fixed_basis(A, m):
    """Orthonormal basis of the fixed subspace of A inside the sum-zero space."""
    M = np.vstack([A - np.eye(m), np.ones((1, m))])
    _, s, vt = np.linalg.svd(M)
    rank = int((s > 1e-9).sum())
    return vt[rank:].T  # columns


def gamma_group(m, kind):
    els = []
    for pi in permutations(range(m)):
        for rev in (0, 1):
            if kind == "N" and rev:
                continue
            if kind == "R" and pi != tuple(range(m)):
                continue
            if kind == "1" and (rev or pi != tuple(range(m))):
                continue
            els.append(matrix(pi, rev, m))
    return els


def element_data(G, m):
    data = []
    for g in G:
        B = fixed_basis(g, m)
        k = B.shape[1]
        powers = {}
        cent_reverses = False
        if k == 1:
            for b in G:
                if np.allclose(b @ g, g @ b):
                    if (B.T @ b @ B)[0, 0] < 0:
                        cent_reverses = True
                        break
        data.append((g, k, cent_reverses))
    return data


def dim_power(g, l, m):
    return fixed_basis(np.linalg.matrix_power(g, l), m).shape[1]


def voter_elements(blocks):
    """Cycle structures of sigma in P = product of S_b: per block a partition of b."""
    def rec(i):
        if i == len(blocks):
            yield ()
            return
        for lam in partitions(blocks[i]):
            for rest in rec(i + 1):
                yield (lam,) + rest
    yield from rec(0)


def stratum_obstruction(sigma, g, k, cent_rev, m):
    lengths = sorted({l for lam in sigma for l in lam})
    dims = {l: dim_power(g, l, m) for l in lengths}
    if k == 0:
        return "stage 0" if all(dims[l] >= 1 for l in lengths) else None
    short_classes = [lam.count(l) for lam in sigma for l in set(lam) if dims[l] == k]
    if k == 1:
        if not short_classes:
            return "stage 1 (connected stratum)"
        if cent_rev and all(c % 2 == 0 for c in short_classes):
            return "stage 1 (May)"
        return None
    if not short_classes:
        return f"stage {k} (Z)"
    gh = reduce(math.gcd, short_classes)
    return f"stage {k} (Z/{gh})" if gh > 1 else None


def describe(sigma):
    return "(" + " | ".join("".join(str(l) for l in lam) for lam in sigma) + ")"


NMAX = 8


def main():
    for m in (3, 4):
        for kind, label in (("N", "neutral"), ("R", "reversal symmetric"), ("NR", "neutral and reversal symmetric")):
            G = gamma_group(m, kind)
            data = element_data(G, m)
            print(f"m = {m}, {label}:")
            for n in range(2, NMAX + 1):
                for blocks in partitions(n):
                    g = reduce(math.gcd, blocks)
                    top = g > 1
                    hits = []
                    for sigma in voter_elements(blocks):
                        if all(set(lam) == {1} for lam in sigma):
                            continue  # sigma = identity: the stratum of gamma alone, handled as below too
                        for (gm, k, cr) in data:
                            ob = stratum_obstruction(sigma, gm, k, cr, m)
                            if ob:
                                cyc = cycle_type([int(np.argmax(gm[:, i] != 0)) for i in range(m)])
                                hits.append(f"{describe(sigma)} with a renaming of cycle type "
                                            f"{''.join(map(str, sorted(cyc, reverse=True)))}"
                                            f"{' and reversal' if np.allclose(gm.sum(axis=0), -1) else ''}: {ob}")
                    # sigma = identity
                    for (gm, k, cr) in data:
                        ob = stratum_obstruction(tuple((1,) * b for b in blocks), gm, k, cr, m)
                        if ob and not (k == m - 1):  # k = m - 1 is gamma acting trivially: the top stage
                            cyc = cycle_type([int(np.argmax(gm[:, i] != 0)) for i in range(m)])
                            hits.append(f"identity on voters with a renaming of cycle type "
                                        f"{''.join(map(str, sorted(cyc, reverse=True)))}"
                                        f"{' and reversal' if np.allclose(gm.sum(axis=0), -1) else ''}: {ob}")
                    hits = sorted(set(hits))
                    mark = "  <- top vanishes, a stratum obstructs" if (not top and hits) else ""
                    if mark or n <= 3:
                        first = hits[0] if hits else "none"
                        print(f"  blocks {str(blocks):14} top {'Z/' + str(g) if top else '0':4}"
                              f"  strata: {len(hits)} obstructing{'; e.g. ' + first if hits else ''}{mark}")
            print()


if __name__ == "__main__":
    main()
