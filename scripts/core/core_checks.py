"""Checks behind the note CORE and the Formal Results.

Part 1  The draw: under uniform removals the last participant is uniform on those present;
        if one participant always calls and is exempt from the draw, they survive with certainty.
Part 2  Electorate conditions, on random profiles with four alternatives: consistency for joint
        draws (L(p+q)(a) >= L(p)(a) + L(q)(a) - 1), SD-participation, and unanimity on first
        choices, for random ballot and for scoring rules with uniform tie-breaking (plurality,
        Borda; antiplurality as a control, which fails unanimity on first choices).
Part 3  Holdings in the sequential variant: for arbitrary behaviour of the groups (each group
        either agrees on some lottery or calls), the value of the whole process equals the
        endowment plus the surplus of every group over its own call, weighted by 1/C(n, |S|).
        Checked on random instances, and on the example of Section 7.1 of the CORE paper.
Plain Python 3; run: python3 core_checks.py
"""
import itertools
import random
from fractions import Fraction as F
from math import comb

random.seed(11)


def survivor_dist(S, exempt=None):
    S = tuple(S)
    if len(S) == 1:
        return {S[0]: F(1)}
    pool = [j for j in S if j != exempt] if exempt in S else list(S)
    out = {}
    for j in pool:
        for k, p in survivor_dist(tuple(x for x in S if x != j), exempt).items():
            out[k] = out.get(k, 0) + p / len(pool)
    return out


def part1():
    print("Part 1: last participant, five participants")
    print("  uniform removals:", {k: str(v) for k, v in sorted(survivor_dist(range(5)).items())})
    print("  participant 0 always calls and is exempt:",
          {k: str(v) for k, v in sorted(survivor_dist(range(5), 0).items())})


def scoring(w, m):
    def rule(p):
        sc = [0] * m
        for r in p:
            for k, c in enumerate(r):
                sc[c] += w[k]
        mx = max(sc)
        W = [c for c in range(m) if sc[c] == mx]
        return {c: F(1, len(W)) for c in W}
    return rule


def random_ballot(p):
    L = {}
    for r in p:
        L[r[0]] = L.get(r[0], 0) + F(1, len(p))
    return L


def part2(m=4, trials=3000):
    print("Part 2: electorate conditions, four alternatives, random profiles")
    R = list(itertools.permutations(range(m)))
    rules = {"random ballot": random_ballot, "plurality": scoring([1, 0, 0, 0], m),
             "Borda": scoring([3, 2, 1, 0], m), "antiplurality": scoring([1, 1, 1, 0], m)}
    for name, f in rules.items():
        okJ = okE = okU = True
        for _ in range(trials):
            p = [random.choice(R) for _ in range(random.randint(1, 5))]
            q = [random.choice(R) for _ in range(random.randint(1, 5))]
            Lp, Lq, Lpq = f(p), f(q), f(p + q)
            okJ &= all(Lpq.get(a, 0) >= Lp.get(a, 0) + Lq.get(a, 0) - 1 for a in range(m))
            v = random.choice(R)
            Lv = f(p + [v])
            okE &= all(sum(Lv.get(a, 0) for a in v[:k]) >= sum(Lp.get(a, 0) for a in v[:k])
                       for k in range(1, m))
            t = random.randrange(m)
            same_top = [r for r in R if r[0] == t]
            okU &= f([random.choice(same_top) for _ in range(random.randint(1, 5))]) == {t: 1}
        print(f"  {name:14s} joint-draw consistency {okJ}, SD-participation {okE}, "
              f"unanimity on first choices {okU}")


def holdings(U, ideal, agree):
    """Recursive values h(S) and surpluses s(S) for a given behaviour of the groups."""
    n = len(U)
    k_out = len(U[0])
    subsets = [frozenset(s) for r in range(1, n + 1) for s in itertools.combinations(range(n), r)]
    h, s = {}, {}
    for S in sorted(subsets, key=len):
        if len(S) == 1:
            j = next(iter(S))
            h[S] = [U[i][ideal[j]] for i in range(n)]
            s[S] = [0.0] * n
            continue
        c = [sum(h[S - {j}][i] for j in S) / len(S) for i in range(n)]
        h[S] = [sum(agree[S][o] * U[i][o] for o in range(k_out)) for i in range(n)] if S in agree else c
        s[S] = [h[S][i] - c[i] for i in range(n)]
    return h, s, subsets


def part3(instances=200):
    print("Part 3: holdings = endowment + sum of surpluses / C(n, |S|)")
    worst = 0.0
    for _ in range(instances):
        n, k_out = random.randint(2, 6), random.randint(2, 5)
        U = [[random.uniform(-1, 1) for _ in range(k_out)] for _ in range(n)]
        ideal = [max(range(k_out), key=lambda o: U[i][o]) for i in range(n)]
        agree = {}
        for r in range(2, n + 1):
            for S in itertools.combinations(range(n), r):
                if random.random() < 0.5:
                    w = [random.random() for _ in range(k_out)]
                    agree[frozenset(S)] = [x / sum(w) for x in w]
        h, s, subsets = holdings(U, ideal, agree)
        e = [sum(U[i][ideal[j]] for j in range(n)) / n for i in range(n)]
        formula = [e[i] + sum(s[S][i] / comb(n, len(S)) for S in subsets if len(S) >= 2)
                   for i in range(n)]
        worst = max(worst, max(abs(a - b) for a, b in zip(h[frozenset(range(n))], formula)))
    print(f"  largest deviation over {instances} random instances: {worst:.1e}")
    # CORE paper, Section 7.1: outcomes A, B, C, D; ideals A, B, C; the pair {2, 3} agrees on D,
    # the other pairs reach no agreement, and the full group calls.
    U = [[10, 5, 5, -100], [0, 10, 0, 9], [0, 0, 10, 9]]
    agree = {frozenset({1, 2}): [0, 0, 0, 1]}
    h, s, subsets = holdings(U, [0, 1, 2], agree)
    pair = frozenset({1, 2})
    e = [sum(U[i][j] for j in range(3)) / 3 for i in range(3)]
    print("  paper's example: endowments", [round(x, 2) for x in e],
          "| surplus of the pair {2, 3}", [round(x, 2) for x in s[pair]],
          "| value of a call", [round(e[i] + s[pair][i] / comb(3, 2), 2) for i in range(3)])


if __name__ == "__main__":
    part1()
    part2()
    part3()
