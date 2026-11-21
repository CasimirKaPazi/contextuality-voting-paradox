"""Consistency of lottery-valued rules: ex ante versus ex post.

A lottery-valued rule L assigns to vote shares p a lottery L(p) over candidates.

Ex ante (population-consistency, Brandl, Brandt and Seedig): if L(p) = L(q),
then L(t p + (1 - t) q) is the same lottery. Maximal lotteries satisfy it.

Ex post: the winners of two electorates and of their union can be drawn
jointly, with the right marginals, so that whenever the two parts elect the
same candidate, the union elects that candidate too. This is the consistency
constraint read as a constraint on a joint draw, i.e. as an empirical model
whose contexts are the triples (p, q, mixture).

Part 1 checks the lemma: a joint draw (X, Y, Z) with X ~ mu, Y ~ nu, Z ~ lam
and "X = Y implies Z = X" exists exactly when lam(a) >= mu(a) + nu(a) - 1 for
every candidate a. (Linear programming against the inequality, random cases.)

Part 2 checks that maximal lotteries violate the inequality: at a profile
without a Condorcet winner, for each candidate a with positive probability,
the blocking construction of A Map of Voting Paradoxes gives an electorate q
with Condorcet winner a and a mixture with Condorcet winner c, so
L(mix)(a) = 0 < L(p)(a) + L(q)(a) - 1 = L(p)(a). The same holds for every rule
that elects a Condorcet winner with certainty.

Part 3 checks that random dictatorship (probability = share of first places),
which is linear in the shares, satisfies the inequality.

Part 4 does the same for participation. Ex post: the winners without and with
an added voter can be drawn jointly so that the added voter never gets a worse
winner; on a ranking this is first-order stochastic dominance (SD) of the
lottery with the voter over the lottery without (checked by linear
programming). Maximal lotteries violate it on random profiles, as every rule
that elects every Condorcet winner must (Brandt, Geist and Peters 2017). Ex
ante: compared by independent draws (pairwise comparison, PC), voting is never
worse (Brandl, Brandt and Hofbauer 2019); checked on the same random cases.
"""
from itertools import permutations, product
import numpy as np
from scipy.optimize import linprog

rng = np.random.default_rng(7)


def joint_exists(mu, nu, lam):
    m = len(mu)
    cells = [(x, y, z) for x, y, z in product(range(m), repeat=3) if x != y or z == x]
    A, b = [], []
    for k, dist in enumerate((mu, nu, lam)):
        for a in range(m):
            A.append([1.0 if c[k] == a else 0.0 for c in cells])
            b.append(dist[a])
    res = linprog(np.zeros(len(cells)), A_eq=np.array(A), b_eq=np.array(b),
                  bounds=[(0, None)] * len(cells), method="highs")
    return res.status == 0


def criterion(mu, nu, lam, tol=1e-9):
    return all(lam[a] >= mu[a] + nu[a] - 1 - tol for a in range(len(mu)))


def margins(shares, orders, n):
    M = np.zeros((n, n))
    for s, o in zip(shares, orders):
        rank = {c: i for i, c in enumerate(o)}
        for i in range(n):
            for j in range(n):
                if i != j:
                    M[i, j] += s if rank[i] < rank[j] else -s
    return M


def condorcet_winner(M):
    for i in range(len(M)):
        if all(M[i, j] > 0 for j in range(len(M)) if j != i):
            return i
    return None


def maximal_lottery(M):
    """Optimal mixed strategy of the symmetric zero-sum game with payoffs M."""
    n = len(M)
    # variables p_1..p_n, v; maximise v subject to (M^T p)_j >= v, sum p = 1
    c = np.zeros(n + 1); c[-1] = -1
    A_ub = np.hstack([-M.T, np.ones((n, 1))])
    res = linprog(c, A_ub=A_ub, b_ub=np.zeros(n), A_eq=[list(np.ones(n)) + [0]], b_eq=[1],
                  bounds=[(0, None)] * n + [(None, None)], method="highs")
    return res.x[:n]


def main():
    print("Part 1: joint draw exists  <=>  lam(a) >= mu(a) + nu(a) - 1 for all a")
    for m in (3, 4, 5):
        agree = total = 0
        for _ in range(400):
            mu, nu, lam = (rng.dirichlet(np.ones(m) * 0.4) for _ in range(3))
            if rng.random() < 0.5:              # concentrate mu and nu on one candidate
                a = rng.integers(m)
                mu = 0.3 * mu; mu[a] += 0.7
                nu = 0.3 * nu; nu[a] += 0.7
            total += 1
            agree += joint_exists(mu, nu, lam) == criterion(mu, nu, lam)
        print(f"  m={m}: {agree}/{total} cases agree")

    print("Part 2: maximal lotteries violate the inequality at every profile with a cycle")
    for n in (3, 4):
        orders = list(permutations(range(n)))
        idx = {o: k for k, o in enumerate(orders)}
        tested = blocked = 0
        while tested < 100:
            p = rng.dirichlet(np.ones(len(orders)) * 0.3)
            Mp = margins(p, orders, n)
            if condorcet_winner(Mp) is not None:
                continue
            L = maximal_lottery(Mp)
            tested += 1
            ok = True
            for a in range(n):
                if L[a] < 1e-9:
                    continue
                c = int(np.argmax(Mp[:, a]))
                rest = [k for k in range(n) if k not in (a, c)]
                worst = max(0.0, max((-Mp[c, d] for d in rest), default=0.0))
                t = 0.5 / (1 + worst)
                d = 0.5 * t * Mp[c, a] / (1 - t)
                q = np.zeros(len(orders))
                q[idx[tuple([a, c] + rest)]] = 0.5 + d / 2
                q[idx[tuple([c, a] + rest)]] = 0.5 - d / 2
                Lq = maximal_lottery(margins(q, orders, n))
                Lz = maximal_lottery(margins(t * p + (1 - t) * q, orders, n))
                ok &= Lq[a] > 1 - 1e-6 and Lz[a] < 1e-6 and Lz[a] < L[a] + Lq[a] - 1
            blocked += ok
        print(f"  n={n}: inequality violated for every candidate in the support at {blocked}/{tested} profiles")

    print("Part 3: random dictatorship satisfies the inequality")
    for n in (3, 4):
        orders = list(permutations(range(n)))
        first = np.array([[1.0 if o[0] == a else 0.0 for o in orders] for a in range(n)])
        ok = True
        for _ in range(1000):
            p, q = rng.dirichlet(np.ones(len(orders))), rng.dirichlet(np.ones(len(orders)))
            t = rng.random()
            ok &= criterion(first @ p, first @ q, first @ (t * p + (1 - t) * q))
        print(f"  n={n}: holds on 1000 random triples: {ok}")
    participation()


def sd_dominates(L1, L0, rank):
    c1 = np.cumsum([L1[a] for a in rank])
    c0 = np.cumsum([L0[a] for a in rank])
    return bool(np.all(c1 >= c0 - 1e-9))


def monotone_draw_exists(L1, L0, rank):
    m = len(rank)
    pos = {a: i for i, a in enumerate(rank)}
    cells = [(x, z) for x in range(m) for z in range(m) if pos[z] <= pos[x]]
    A, b = [], []
    for a in range(m):
        A.append([1.0 if c[0] == a else 0.0 for c in cells]); b.append(L0[a])
        A.append([1.0 if c[1] == a else 0.0 for c in cells]); b.append(L1[a])
    res = linprog(np.zeros(len(cells)), A_eq=np.array(A), b_eq=np.array(b),
                  bounds=[(0, None)] * len(cells), method="highs")
    return res.status == 0


def pc_advantage(L1, L0, rank):
    """P(draw from L1 beats draw from L0) - P(the reverse), independent draws."""
    pos = {a: i for i, a in enumerate(rank)}
    return sum(L1[a] * L0[b] - L0[a] * L1[b]
               for a in range(len(rank)) for b in range(len(rank)) if pos[a] < pos[b])


def participation():
    print("Part 4: participation, ex post (SD) and ex ante (PC)")
    agree = 0
    for _ in range(500):
        L0, L1 = rng.dirichlet(np.ones(4)), rng.dirichlet(np.ones(4))
        rank = list(rng.permutation(4))
        if rng.random() < 0.5:
            L1 = 0.5 * L1 + 0.5 * L0; L1[rank[0]] += 0.05; L1 /= L1.sum()
        agree += sd_dominates(L1, L0, rank) == monotone_draw_exists(L1, L0, rank)
    print(f"  SD dominance <=> joint draw in which voting never hurts: {agree}/500 agree")
    for n in (3, 4):
        orders = list(permutations(range(n)))
        sd_fail, worst_pc = 0, 1.0
        for _ in range(3000):
            p = rng.dirichlet(np.ones(len(orders)) * 0.3)
            k = rng.integers(len(orders))
            eps = 10 ** rng.uniform(-3, -0.5)
            q = (p + eps * np.eye(len(orders))[k]) / (1 + eps)
            L0 = maximal_lottery(margins(p, orders, n))
            L1 = maximal_lottery(margins(q, orders, n))
            rank = list(orders[k])
            sd_fail += not sd_dominates(L1, L0, rank)
            worst_pc = min(worst_pc, pc_advantage(L1, L0, rank))
        print(f"  n={n}, maximal lotteries, 3000 random additions of a voter: "
              f"SD-participation fails {sd_fail} times; smallest PC advantage of voting {worst_pc:.1e}")


if __name__ == "__main__":
    main()
