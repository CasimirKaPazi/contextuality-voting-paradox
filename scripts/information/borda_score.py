"""Borda against score under the common rationale (*Borda and Score*).

Value of a ballot s: sum over candidates of s(x) c(x), with c(x) = sum_y p(x, y)(u_x - u_y).  The
best Borda ballot ranks the candidates by c(x) (rearrangement inequality); the best score ballot
gives k to x when c(x) > 0 and 0 otherwise.  In the corner (T), with the ties of the other candidates
with the leader equally likely, the Borda ballot puts the preferred front-runner first, the other
front-runner last and the rest in sincere order; the score ballot is the approval ballot of the
leader rule, times k.

1. Stage 2 in bits in that corner, impartial culture, exact over all rankings.
2. The walk of polls in the corner (the next poll is the top two of the strategic Borda tallies),
   101 voters, 200 profiles per model, from every ordered pair of front-runners: whether the
   Condorcet winner ends as the steady leader.  For three candidates, also the rule of Proposition 4:
   the next poll is (winner of a1 against a2, the third candidate).
3. Away from the corner: weights P0 + lam R as in stage2_bits.py.
About two and a half minutes.
"""
import itertools
from collections import Counter
from math import log2
import numpy as np


def H(xs):
    c, n = Counter(xs), len(xs)
    return -sum(v / n * log2(v / n) for v in c.values())


def Hc(a, b):
    return H(list(zip(a, b))) - H(list(b))


def borda_corner(rank, a1, a2):
    pos = {c: i for i, c in enumerate(rank)}
    top, bottom = (a1, a2) if pos[a1] < pos[a2] else (a2, a1)
    return (top,) + tuple(c for c in rank if c not in (a1, a2)) + (bottom,)


def approval_corner(rank, a1, a2):
    pos = {c: i for i, c in enumerate(rank)}
    return tuple(int(pos[x] < pos[a1]) if x != a1 else int(pos[a1] < pos[a2]) for x in range(len(rank)))


def bits_corner():
    print("1. corner (T) with equally likely ties of the other candidates, impartial culture, exact")
    for m in range(3, 7):
        B, A = [], []
        for r in itertools.permutations(range(m)):
            B.append(borda_corner(r, 0, 1))
            A.append(approval_corner(r, 0, 1))
        print(f"   m = {m}: capacities {log2(len(B)):.2f} and {m * log2(m):.2f} bits (k = m - 1); "
              f"H(Borda) {H(B):.3f}, H(score) {H(A):.3f}, H(Borda | score) {Hc(B, A):.3f}, "
              f"H(score | Borda) {Hc(A, B):.3f}")


def next_poll(ranks, m, a1, a2):
    T = np.zeros(m)
    for r in ranks:
        for i, c in enumerate(borda_corner(r, a1, a2)):
            T[c] += m - 1 - i
    o = np.argsort(-T, kind='stable')
    return int(o[0]), int(o[1]), T


def beats(U, x, y):
    return (U[:, x] > U[:, y]).sum() > len(U) / 2


def condorcet_winner(U, m):
    for x in range(m):
        if all(beats(U, x, y) for y in range(m) if y != x):
            return x


def walks(profiles=200, rounds=40):
    print("2. walks of polls in the corner, 101 voters")
    rng = np.random.default_rng(2)
    for model in ('ic', 'spatial'):
        for m in (3, 4, 5):
            S, rule3, self_conf = Counter(), True, 0
            for _ in range(profiles):
                if model == 'ic':
                    U = rng.random((101, m))
                else:
                    c, V = rng.normal(size=(m, 2)), rng.normal(size=(101, 2))
                    U = -np.linalg.norm(V[:, None] - c[None], axis=2)
                ranks = [tuple(np.argsort(-u)) for u in U]
                w = condorcet_winner(U, m)
                for a1, a2 in itertools.permutations(range(m), 2):
                    b1, b2, T = next_poll(ranks, m, a1, a2)
                    self_conf += (b1, b2) == (a1, a2) and beats(U, a1, a2)
                    if m == 3:
                        win = a1 if beats(U, a1, a2) else a2
                        rule3 &= (b1, b2) == (win, 3 - a1 - a2)
                    if w is None:
                        continue
                    leaders, x, y = [], a1, a2
                    for _ in range(rounds):
                        x, y, _ = next_poll(ranks, m, x, y)
                        leaders.append(x)
                    last = set(leaders[-20:])
                    S['stays' if last == {w} else 'among' if w in last else 'absent'] += 1
            tot = sum(S.values())
            line = (f"   {model:8s} m = {m}: Condorcet winner the steady leader {S['stays']}/{tot}, "
                    f"among the leaders of a cycle {S['among']}, absent {S['absent']}; "
                    f"self-confirming polls with a1 beating a2: {self_conf}")
            if m == 3:
                line += f"; rule of Proposition 4 {'ok' if rule3 else 'FAIL'}"
            print(line)


def away(trials=40):
    print("3. away from the corner: P = P0 + lam R")
    rng = np.random.default_rng(2)
    for m in (3, 4, 5):
        for lam in (0, 0.01, 0.1, 1):
            R = []
            for _ in range(trials):
                P0 = np.zeros((m, m))
                P0[0, 1] = P0[1, 0] = 1
                for x in range(2, m):
                    P0[x, 0] = P0[0, x] = 1e-3
                W = rng.random((m, m)) ** 3
                Rm = (W + W.T) / 2
                np.fill_diagonal(Rm, 0)
                Pm = P0 + lam * Rm
                U = rng.random((3000, m))
                C = np.stack([sum(Pm[x, y] * (U[:, x] - U[:, y]) for y in range(m) if y != x)
                              for x in range(m)], 1)
                B, A = [tuple(np.argsort(-c)) for c in C], [tuple(r) for r in (C > 0).astype(int)]
                R.append((H(B), H(A), Hc(B, A), Hc(A, B)))
            R = np.array(R).mean(0)
            print(f"   m = {m}, lam = {lam:<4}: H(Borda) {R[0]:.3f}, H(score) {R[1]:.3f}, "
                  f"H(Borda | score) {R[2]:.3f}, H(score | Borda) {R[3]:.3f}")


if __name__ == "__main__":
    bits_corner()
    walks()
    away()
