"""Stage 2 in bits for plurality, approval and score (*Plurality and Approval*, Section 11;
*Score and Approval*, Section 3; *Strategic Information*, README, Section 2).

By the lemma of the README, Section 2, Blackwell's order at a poll holds exactly when one strategic
ballot is a function of the other, voter by voter; the conditional entropy H(A | B) says how far it
fails.  Entropies are in bits, over a distribution of voters.

1. Corner (T), impartial culture, exact over all rankings: H(plurality) = 1, H(plurality | approval)
   = 0, and H(approval) = log2 m + (1/m) sum_j log2 C(m-1, j).  Spatial model (30 profiles, 4000
   voters): the same zero.
2. Away from the corner: weights P = P0 + lam R, where P0 has the tie of the front-runners at 1 and
   the ties of the other candidates with the leader at 0.001, and R is random as in
   strategic_information.py; ballots from the coefficients c(x) (Proposition 5).
3. Laslier's model of uncounted marks with 100 other voters: exact best replies at fixed polls and at
   polls from impartial-culture profiles whose approval tallies have the front-runners on top.
4. Score (0..k) against approval in Laslier's model with the others voting 0 or k (shares 0.55, 0.45,
   0.35), 10 to 40 others.
Ties between best ballots are broken towards the most sincere ballot.  About eight minutes.
"""
import itertools
import random
from collections import Counter
from math import comb, log2
import numpy as np
from ballot_mistakes import best_replies
from score_exact import best as score_best


def H(xs):
    c, n = Counter(xs), len(xs)
    return -sum(v / n * log2(v / n) for v in c.values())


def Hc(a, b):
    return H(list(zip(a, b))) - H(list(b))


def pick(cands, u):
    return max(cands, key=lambda b: (sum(x * y for x, y in zip(b, u)), b))


def leader_rule(rank, a1, a2):
    pos = {c: i for i, c in enumerate(rank)}
    appr = tuple(int(pos[x] < pos[a1]) if x != a1 else int(pos[a1] < pos[a2]) for x in range(len(rank)))
    return (a1 if pos[a1] < pos[a2] else a2), appr


def corner():
    print("1. corner (T), impartial culture, exact")
    for m in range(3, 7):
        L = [leader_rule(r, 0, 1) for r in itertools.permutations(range(m))]
        P, A = [x[0] for x in L], [x[1] for x in L]
        formula = log2(m) + sum(log2(comb(m - 1, j)) for j in range(m)) / m
        print(f"   m = {m}: capacities {log2(m):.2f} and {m} bits; H(plur) {H(P):.3f}, H(appr) {H(A):.3f} "
              f"(formula {formula:.3f}), H(plur | appr) {Hc(P, A):.3f}, H(appr | plur) {Hc(A, P):.3f}")
    rng = np.random.default_rng(3)
    print("   spatial model, 30 profiles, poll (0, 1)")
    for m in range(3, 7):
        R = []
        for _ in range(30):
            cand, V = rng.normal(size=(m, 2)), rng.normal(size=(4000, 2))
            U = -np.linalg.norm(V[:, None] - cand[None], axis=2)
            L = [leader_rule(tuple(np.argsort(-u)), 0, 1) for u in U]
            P, A = [x[0] for x in L], [x[1] for x in L]
            R.append((H(P), H(A), Hc(P, A), Hc(A, P)))
        R = np.array(R)
        print(f"   m = {m}: H(plur) {R[:, 0].mean():.3f}, H(appr) {R[:, 1].mean():.3f}, "
              f"H(plur | appr) {R[:, 2].max():.3f} at most, H(appr | plur) {R[:, 3].mean():.3f}")


def away(trials=40):
    print("2. away from the corner: P = P0 + lam R (40 weight systems, 3000 voters each)")
    rng = np.random.default_rng(4)
    for m in (3, 4, 5):
        for lam in (0, 0.01, 0.03, 0.1, 0.3, 1):
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
                P, A = list(np.argmax(C, 1)), [tuple(r) for r in (C > 0).astype(int)]
                R.append((H(P), H(A), Hc(P, A), Hc(A, P)))
            R = np.array(R).mean(0)
            print(f"   m = {m}, lam = {lam:<4}: H(plur) {R[0]:.3f}, H(appr) {R[1]:.3f}, "
                  f"H(plur | appr) {R[2]:.3f}, H(appr | plur) {R[3]:.3f}")


def laslier(polls=30, voters=300):
    print("3. Laslier's model of uncounted marks, 100 other voters")
    random.seed(9)
    fixed = ((3, [55, 45, 35]), (4, [55, 45, 35, 20]), (3, [52, 48, 30]), (3, [52, 48, 45]))
    for m, at in fixed:
        pt = at[:2] + [0] * (m - 2)
        pl = [tuple(int(i == x) for i in range(m)) for x in range(m)]
        ap = list(itertools.product((0, 1), repeat=m))
        vs = [random.sample(range(1, 1000), m) for _ in range(400)]
        P = [pick(best_replies(pt, u, pl), u) for u in vs]
        A = [pick(best_replies(at, u, ap), u) for u in vs]
        print(f"   approval poll {at}: H(plur | appr) {Hc(P, A):.4f}, H(appr | plur) {Hc(A, P):.3f}; "
              f"ballots approving both front-runners or neither: {sum(a[0] == a[1] for a in A)}/400")
    random.seed(4)
    for m in (3, 4):
        R = []
        while len(R) < polls:
            prof = [random.sample(range(1, 1000), m) for _ in range(100)]
            n01 = sum(u[0] > u[1] for u in prof)
            at = [n01, 100 - n01] + [sum(u[x] > u[0] for u in prof) for x in range(2, m)]
            if not (n01 > 50 and at[1] > max(at[2:])):
                continue
            pt = [n01, 100 - n01] + [0] * (m - 2)
            pl = [tuple(int(i == x) for i in range(m)) for x in range(m)]
            ap = list(itertools.product((0, 1), repeat=m))
            vs = [random.sample(range(1, 1000), m) for _ in range(voters)]
            P = [pick(best_replies(pt, u, pl), u) for u in vs]
            A = [pick(best_replies(at, u, ap), u) for u in vs]
            R.append((H(P), H(A), Hc(P, A), Hc(A, P)))
        R = np.array(R)
        print(f"   m = {m}, {polls} polls from impartial culture: H(plur) {R[:, 0].mean():.3f}, "
              f"H(appr) {R[:, 1].mean():.3f}, H(plur | appr) {R[:, 2].mean():.3f} "
              f"(max {R[:, 2].max():.3f}, zero at {(R[:, 2] < 1e-9).sum()}), H(appr | plur) {R[:, 3].mean():.3f}")


def score(voters=300):
    print("4. score (0..k) against approval, Laslier's model, others voting 0 or k, shares 0.55, 0.45, 0.35")
    random.seed(4)
    for k in (2, 3):
        for N in (10, 20, 40):
            counts = [round(s * N) for s in (0.55, 0.45, 0.35)]
            vs = [random.sample(range(1, 1000), 3) for _ in range(voters)]
            S = [pick(score_best(counts, u, k), u) for u in vs]
            A = [pick(score_best(counts, u, 1), u) for u in vs]
            same = sum(tuple(x * k for x in a) == s for s, a in zip(S, A))
            print(f"   k = {k}, N = {N}: H(score) {H(S):.3f}, H(appr) {H(A):.3f}, H(score | appr) "
                  f"{Hc(S, A):.3f}, H(appr | score) {Hc(A, S):.3f}; score ballot = k times approval ballot "
                  f"for {same}/{voters}")


if __name__ == "__main__":
    corner()
    away()
    laslier()
    score()
