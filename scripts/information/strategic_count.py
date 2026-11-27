"""The strategic count as a linear map (*Strategic Information*, README, Sections 2 and 6).

At a fixed poll every voter type casts one ballot, and the count is additive over voters, so the
strategic count is a linear map M of the histogram of types.  The strategic count of method A is a
function of that of method B on every profile exactly when every row of M_A is a combination of rows
of M_B (README, Section 2, Proposition).  The rank of M, not counting the size of the electorate, is
the number of independent numbers about the electorate that the strategic count keeps.

1. Corner (T), types = rankings, poll (0, 1): ranks for plurality, approval (score is k times
   approval) and Borda (with (E), *Borda and Score*, Section 2), the containments, and whether a voter
   and the reversed voter together add the same to the count whatever the voter (README, Section 6).
2. Three candidates, corner polls of instant runoff and of BTR-plurality (count = histogram of
   rankings): ranks, whether the plurality count at the poll of the two finalists is contained, and
   the reversal pairs.
3. Stage 1: a profile of rankings to which a ballot and its reverse are added, up to three times, changing
   the winner of instant runoff and of BTR-plurality, with no ties before or after.
A few seconds.
"""
import itertools
import numpy as np
from borda_score import borda_corner, approval_corner
from irv_three import best_irv, polls as irv_polls, RANKINGS
from btr_three import best_btr, btr_polls


def rank(M):
    return int(np.linalg.matrix_rank(M))


def inside(A, B):
    """Every row of A is a combination of rows of B."""
    return rank(np.vstack([A, B])) == rank(B)


def pairs_constant(M, types):
    idx = {t: i for i, t in enumerate(types)}
    return len({tuple(M[:, idx[t]] + M[:, idx[t[::-1]]]) for t in types}) == 1


def additive():
    print("1. corner (T), poll (0, 1); ranks do not count the size of the electorate")
    for m in (3, 4, 5, 6):
        types = list(itertools.permutations(range(m)))
        ones = np.ones((1, len(types)))
        P, A, B = (np.zeros((m, len(types))) for _ in range(3))
        for j, r in enumerate(types):
            P[0 if r.index(0) < r.index(1) else 1, j] = 1
            A[:, j] = approval_corner(r, 0, 1)
            for i, c in enumerate(borda_corner(r, 0, 1)):
                B[c, j] = m - 1 - i
        P, A, B = (np.vstack([X, ones]) for X in (P, A, B))
        common = rank(A) + rank(B) - rank(np.vstack([A, B])) - 1
        print(f"   m = {m}: rank plurality {rank(P) - 1}, approval {rank(A) - 1}, Borda {rank(B) - 1}; "
              f"plurality in approval {inside(P, A)}, Borda in approval {inside(B, A)}, approval in Borda "
              f"{inside(A, B)}, common to Borda and approval {common}; reversal pairs add a constant: "
              f"plurality {pairs_constant(P, types)}, approval {pairs_constant(A, types)}, "
              f"Borda {pairs_constant(B, types)}")


def ranked():
    print("2. three candidates, corner polls of the ranked methods (F before E)")
    types = RANKINGS
    U = {r: [3 - r.index(c) for c in range(3)] for r in types}

    def hist(best, poll):
        M = np.zeros((6, 6))
        for j, r in enumerate(types):
            M[types.index(best(U[r], poll, 'F')), j] = 1
        return M

    seen = set()
    for poll in irv_polls():
        L, R = poll[0], poll[1]
        M = hist(best_irv, poll)
        Pl = np.zeros((3, 6))
        for j, r in enumerate(types):
            Pl[L if r.index(L) < r.index(R) else R, j] = 1
        seen.add((rank(M) - 1, inside(Pl, M), pairs_constant(M, types)))
    print("   instant runoff, over all polls: (rank, plurality count contained, reversal pairs add a "
          "constant):", sorted(seen))
    seen = {(rank(hist(best_btr, poll)) - 1, pairs_constant(hist(best_btr, poll), types))
            for poll in btr_polls()}
    print("   BTR-plurality, over all polls: (rank, reversal pairs add a constant):", sorted(seen))


def irv(h):
    f = [sum(n for r, n in h.items() if r[0] == c) for c in range(3)]
    if len(set(f)) < 3:
        return None
    e = f.index(min(f))
    x, y = [c for c in range(3) if c != e]
    a = sum(n for r, n in h.items() if r.index(x) < r.index(y))
    b = sum(h.values()) - a
    return None if a == b else (x if a > b else y)


def btr(h):
    f = [sum(n for r, n in h.items() if r[0] == c) for c in range(3)]
    if len(set(f)) < 3:
        return None
    b, m, t = sorted(range(3), key=lambda c: f[c])
    n = sum(h.values())

    def duel(x, y):
        a = sum(k for r, k in h.items() if r.index(x) < r.index(y))
        return None if 2 * a == n else (x if 2 * a > n else y)

    s = duel(b, m)
    return None if s is None else duel(s, t)


def reversal_example():
    print("3. a ballot and its reverse, added up to three times, change the winner (rankings best first)")
    for name, rule in (("instant runoff", irv), ("BTR-plurality", btr)):
        for counts in itertools.product(range(5), repeat=6):
            h = dict(zip(RANKINGS, counts))
            w = rule(h)
            if w is None:
                continue
            found = False
            for r, k in itertools.product(RANKINGS[:3], (1, 2, 3)):
                g = dict(h)
                g[r] += k
                g[r[::-1]] += k
                w2 = rule(g)
                if w2 is not None and w2 != w:
                    print(f"   {name}: {{{', '.join(f'{n} x {t}' for t, n in h.items() if n)}}} elects {w}; "
                          f"with {k} x {r} and {k} x {r[::-1]} added it elects {w2}")
                    found = True
                    break
            if found:
                break


if __name__ == "__main__":
    additive()
    ranked()
    reversal_example()
