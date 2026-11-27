"""Equality of voters and alternatives with equal rankings allowed (weak orders).

Checks Section 6 of notes/equality-of-voters-and-alternatives.md:
  1. three voters, four candidates: a tie of maximal lotteries in an odd electorate that no single
     added ballot (of 75) settles, while twice the profile plus any strict ballot is settled;
  2. survey for four candidates with margins in -1..1: how many ties one ballot settles;
  3. Proposition 8 on random profiles of weak orders: k times the profile plus any strict ballot has
     a unique maximal lottery for k >= 2, and every even Pfaffian is +-1 modulo k;
  4. two candidates that no ballot distinguishes: cloning one of them changes the shares;
  5. the tie-breaker "random voters in turn, then a random order of the candidates": independent of
     clones on random profiles whenever no outsider is ranked equal to the cloned candidate on every
     ballot; what the voters leave open is only the division among candidates no ballot distinguishes.
Run: python3 equality_equal_rankings.py   (needs numpy and scipy; about three minutes)
"""
import itertools
import math
import numpy as np
from scipy.optimize import linprog

rng = np.random.default_rng(11)


# ---------- weak orders: a ballot gives each candidate a level, 0 is the top ----------

def weak_orders(m):
    return [t for t in itertools.product(range(m), repeat=m) if set(t) == set(range(max(t) + 1))]


def canonical(levels):
    vals = sorted(set(levels))
    return tuple(vals.index(v) for v in levels)


def ballot_margins(ballot):
    lev = np.array(ballot)
    return np.sign(lev[None, :] - lev[:, None]).astype(float)       # +1 where the row is above the column


def margins(profile, m):
    return sum((ballot_margins(r) for r in profile), np.zeros((m, m)))


def classes(ballot):
    return [[x for x in range(len(ballot)) if ballot[x] == lev] for lev in range(max(ballot) + 1)]


def show(ballot, names="abcdef"):
    return " > ".join("=".join(names[x] for x in cl) for cl in classes(ballot))


# ---------- maximal lotteries ----------

def lp(G, objective, A_eq=None, b_eq=None):
    m = len(G)
    A_eq = [np.ones(m)] if A_eq is None else A_eq
    b_eq = [1.0] if b_eq is None else b_eq
    return linprog(objective, A_ub=-G.T, b_ub=np.zeros(m), A_eq=np.array(A_eq), b_eq=b_eq,
                   bounds=(0, 1), method="highs").x


def single_point(G, A_eq=None, b_eq=None):
    """The lottery if the constraints leave exactly one maximal lottery, otherwise None."""
    c = rng.normal(size=len(G))
    u, v = lp(G, c, A_eq, b_eq), lp(G, -c, A_eq, b_eq)
    return u if np.allclose(u, v, atol=1e-7) else None


def unique(G):
    return single_point(G) is not None


def skew(m, upper):
    G = np.zeros((m, m))
    for (i, j), v in zip(itertools.combinations(range(m), 2), upper):
        G[i, j], G[j, i] = v, -v
    return G


def pfaffian(M):
    n = len(M)
    if n == 0:
        return 1
    total = 0
    for j in range(1, n):
        if M[0][j]:
            rest = [k for k in range(1, n) if k != j]
            total += (-1) ** (j - 1) * M[0][j] * pfaffian([[M[r][c] for c in rest] for r in rest])
    return total


# ---------- the tie-breaker: random voters in turn, then a random order of the candidates ----------

def narrow(G, A_eq, b_eq, class_list):
    """Keep the lotteries that are best for an order of classes: the largest total for the first
    class, then the largest for the second, and so on."""
    A_eq, b_eq = list(A_eq), list(b_eq)
    for cl in class_list[:-1]:
        e = np.zeros(len(G))
        e[list(cl)] = 1
        A_eq.append(e)
        b_eq.append(lp(G, -e, A_eq[:-1], b_eq) @ e)
    return A_eq, b_eq


def left_open(G, A_eq, b_eq, groups):
    """What all voters leave open. Checks that it is only the division within groups of candidates
    that no ballot distinguishes, then lets a uniformly random order of the candidates decide."""
    m = len(G)
    points = [lp(G, rng.normal(size=m), A_eq, b_eq) for _ in range(6)]
    totals = [[p[g].sum() for g in groups] for p in points]
    assert np.allclose(totals, totals[0], atol=1e-7)
    out = np.zeros(m)
    for order in itertools.permutations(range(m)):
        A, b = narrow(G, A_eq, b_eq, [[x] for x in order])
        out += lp(G, np.zeros(m), A, b)
    return out / math.factorial(m)


def chain(G, A_eq, b_eq, types, groups):
    """Voters are drawn until every ballot has come up; each new ballot narrows the set. The next new
    ballot is t with probability share(t) / (share of the ballots not yet drawn)."""
    point = single_point(G, A_eq, b_eq)
    if point is not None:
        return point
    if not types:
        return left_open(G, A_eq, b_eq, groups)
    total, out = sum(types.values()), np.zeros(len(G))
    for t, count in types.items():
        A, b = narrow(G, A_eq, b_eq, classes(t))
        out += count / total * chain(G, A, b, {u: v for u, v in types.items() if u != t}, groups)
    return out


def rule(profile, m):
    """Maximal lotteries, ties broken by random voters in turn and then a random order of candidates."""
    types = {}
    for r in profile:
        types[r] = types.get(r, 0) + 1
    signature = [tuple(r[x] for r in profile) for x in range(m)]
    groups = [[x for x in range(m) if signature[x] == s] for s in sorted(set(signature))]
    return chain(margins(profile, m), [np.ones(m)], [1.0], types, groups)


# ---------- 1. a tie that no single ballot settles ----------
W4 = weak_orders(4)
stuck = [(0, 1, 0, 1), (1, 0, 3, 2), (3, 2, 1, 0)]         # a=c > b=d;  b > a > d > c;  d > c > b > a
G = margins(stuck, 4)
print("1. profile:", "; ".join(show(r) for r in stuck))
print("   margins (ab, ac, ad, bc, bd, cd):", [int(G[i, j]) for i, j in itertools.combinations(range(4), 2)])
assert not unique(G)
ends = lp(G, np.array([-1.0, 0, 0, 0])), lp(G, np.array([1.0, 0, 0, 0]))
print(f"   maximal lotteries: the segment from {np.abs(ends[0]).round(3)} to {np.abs(ends[1]).round(3)}")
settled_by = [r for r in W4 if unique(G + ballot_margins(r))]
print(f"   added ballots that give a unique maximal lottery: {len(settled_by)} of {len(W4)}")
assert not settled_by
strict4 = [r for r in W4 if max(r) == 3]
assert all(unique(k * G + ballot_margins(r)) for r in strict4 for k in (2, 3, 4))
print(f"   twice, three and four times the profile plus one strict ballot: unique for all {len(strict4)} ballots")

# ---------- 2. survey: four candidates, margins in -1..1 ----------
undecided = one_ballot = 0
for upper in itertools.product([-1, 0, 1], repeat=6):
    G = skew(4, upper)
    if not unique(G):
        undecided += 1
        one_ballot += any(unique(G + ballot_margins(r)) for r in W4)
print(f"2. four candidates, margins in -1..1: {undecided} ties, {one_ballot} settled by one ballot,"
      f" {undecided - one_ballot} not (the profile of part 1 and its renamings)")
assert undecided - one_ballot == 6

# ---------- 3. Proposition 8 ----------
assert all(pfaffian([[(j > i) - (j < i) for j in range(n)] for i in range(n)]) == 1 for n in (2, 4, 6))
for m, trials in [(4, 120), (5, 60)]:
    W = weak_orders(m)
    strict = [r for r in W if max(r) == m - 1]
    ties = 0
    for _ in range(trials):
        prof = [W[i] for i in rng.integers(len(W), size=int(rng.integers(1, 7)))]
        G = margins(prof, m)
        ties += not unique(G)
        for k in (2, 3, 7):
            r = strict[rng.integers(len(strict))]
            M = k * G + ballot_margins(r)
            assert unique(M)
            for size in range(2, m + 1, 2):
                for S in itertools.combinations(range(m), size):
                    assert pfaffian([[int(M[i, j]) for j in S] for i in S]) % k in (1, k - 1)
    print(f"3. {m} candidates, {trials} random profiles of weak orders ({ties} ties): k times the profile plus a"
          " strict ballot is unique for k = 2, 3, 7; even Pfaffians are +-1 modulo k")

# ---------- 4. candidates that no ballot distinguishes ----------
before = [(0, 0, 1)]                                       # a = x > z
after = [(0, 0, 1, 0)]                                     # a = x = x' > z
L, L2 = rule(before, 3), rule(after, 4)
print(f"4. a = x > z: (a, x, z) = {np.abs(L).round(3)}; with x cloned, a = x = x' > z: a {L2[0]:.3f},"
      f" the group x, x' {L2[1] + L2[3]:.3f}")
assert np.isclose(L[1], 0.5) and np.isclose(L2[1] + L2[3], 2 / 3)

# ---------- 5. the tie-breaker under cloning ----------
def clone(profile, x, m):
    """x' is placed with x: ranked equal to x where x shares its level, otherwise equal, just above
    or just below."""
    out = []
    for r in profile:
        shared = any(r[y] == r[x] for y in range(m) if y != x)
        level = r[x] if shared or rng.random() < 0.4 else r[x] + rng.choice([-0.5, 0.5])
        out.append(canonical(list(r) + [level]))
    return out


for m, trials in [(3, 400), (4, 150)]:
    W = weak_orders(m)
    ties = same = same_fail = 0
    for _ in range(trials):
        prof = [W[i] for i in rng.integers(len(W), size=int(rng.integers(1, 6)))]
        x = int(rng.integers(m))
        cloned = clone(prof, x, m)
        L, L2 = rule(prof, m), rule(cloned, m + 1)
        merged = L2[:m].copy()
        merged[x] += L2[m]
        ties += not unique(margins(cloned, m + 1))
        if any(all(r[y] == r[x] for r in prof) for y in range(m) if y != x):
            same += 1
            same_fail += not np.allclose(merged, L, atol=1e-7)
        else:
            assert np.allclose(merged, L, atol=1e-7)
    print(f"5. {m} candidates, one cloned, {trials} random profiles ({ties} with a tie after cloning):"
          f" independent of clones in all {trials - same} cases where every outsider is distinguished from"
          f" the cloned candidate by some ballot; of the other {same}, {same_fail} fail")
print("all checks passed")
