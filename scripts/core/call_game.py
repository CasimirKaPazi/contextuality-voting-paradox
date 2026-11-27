"""The call structure as a game with random recognition (CORE note, Section 3g).

At every group S the process reaches, one member is drawn uniformly and proposes a lottery over the
outcomes; then every member accepts or calls. If all accept, the lottery is enacted; otherwise one
member is drawn uniformly and removed, and the game goes on at the smaller group. A single member
enacts their ideal. Utilities are known to everyone.

Backward induction over the groups: given the outcome law from every smaller group, accepting exactly
the proposals worth at least the call is weakly dominant, and the proposer's best acceptable lottery is
a linear program. Ties are broken towards the other members, as in bargaining_rules.best_for.

Part 1: the outcome of this game, computed node by node with the acceptance checked, equals the Raiffa
        one-step rule of bargaining_rules.py in every group (holdings compared).
Part 2: how much the proposer's choice is left open: at how many proposal nodes the proposer's optimal
        lotteries give the other members different values, and by how much; and the same over every other
        participant, members and those already removed. Uniqueness of the equilibrium values needs the
        second: a removed participant's value for a smaller group enters their call at the larger groups.
Part 3: what recognition is worth: the proposer's gain over the ex ante value of the group, in units of
        utility range.
Run: python3 call_game.py   (numpy and scipy; a few minutes)
"""
import itertools
import numpy as np
from scipy.optimize import linprog

from bargaining_rules import best_for, holdings, families

TOL = 1e-10


def opt_face_spread(A, d, m, others):
    """Largest spread, over the utilities in `others`, of their value on the proposer's optimal face."""
    s, K = A.shape
    base = dict(A_eq=np.ones((1, K)), b_eq=[1], bounds=(0, 1), method="highs")
    v = -linprog(-A[m], A_ub=-A, b_ub=-(d - TOL), **base).fun
    A_ub = np.vstack([-A, -A[m:m + 1]]); b_ub = np.r_[-(d - TOL), -(v - 1e-9)]
    spread = 0.0
    for u in others:
        lo = linprog(u, A_ub=A_ub, b_ub=b_ub, **base).fun
        hi = -linprog(-u, A_ub=A_ub, b_ub=b_ub, **base).fun
        spread = max(spread, (hi - lo) / (u.max() - u.min()))
    return spread


def game(U, spreads=None, gains=None, spreads_all=None):
    n, K = U.shape
    ideal = U.argmax(1)
    D = {frozenset([j]): np.eye(K)[ideal[j]] for j in range(n)}
    for r in range(2, n + 1):
        for S in map(frozenset, itertools.combinations(range(n), r)):
            mem = sorted(S); A = U[mem]
            c = sum(D[S - {k}] for k in S) / r          # the call
            d = A @ c
            props = []
            for m in range(r):
                x = best_for(A, d - TOL, m)
                assert (A @ x >= d - 1e-7).all()         # every member accepts
                props.append(x)
                if spreads is not None:
                    spreads.append(opt_face_spread(A, d, m, [A[k] for k in range(r) if k != m]))
                if spreads_all is not None:
                    spreads_all.append(opt_face_spread(A, d, m, [U[j] for j in range(n) if j != mem[m]]))
            D[S] = np.mean(props, axis=0)
            if gains is not None and r == n:
                ex = A @ D[S]
                gains.extend(((A[m] @ props[m] - ex[m]) / (A[m].max() - A[m].min())) for m in range(r))
    return U @ D[frozenset(range(n))]


def main(sizes=((3, 5, 30), (4, 6, 20), (5, 7, 6)), seed=8):
    rng = np.random.default_rng(seed)
    for fam, gen in families(rng).items():
        diff, spreads, gains, spreads_all = 0.0, [], [], []
        for n, K, T in sizes:
            for _ in range(T):
                U = gen(n, K)
                h = game(U, spreads, gains, spreads_all)
                diff = max(diff, np.abs(h - holdings(U, "Raiffa 1")).max())
        sp = np.array(spreads); sa = np.array(spreads_all); g = np.array(gains)
        print(f"{fam}:")
        print(f"   part 1: largest |game - Raiffa one step| {diff:.1e}")
        print(f"   part 2: proposal nodes {len(sp)}, open choice for others at {np.mean(sp > 1e-6):.2f} of them, "
              f"largest spread {sp.max():.3f}")
        # threshold 1e-5: the solver's tolerances leave spreads of order 1e-6 for removed participants
        print(f"           over every other participant: open at {np.mean(sa > 1e-5):.2f} of them, "
              f"largest spread {sa.max():.3f}")
        print(f"   part 3: proposer's gain over the ex ante value at the full group: mean {g.mean():.3f}, "
              f"largest {g.max():.3f}")


if __name__ == "__main__":
    main()
