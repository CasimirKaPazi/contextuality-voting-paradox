"""Equality of voters and alternatives with equal rankings allowed (weak orders).

Checks Section 6 of notes/equality-of-voters-and-alternatives.md:
  1. three voters, four candidates: a tie of maximal lotteries in an odd electorate that no single
     added ballot (of 75) settles, while twice the profile plus any strict ballot is settled;
  2. survey for four candidates with margins in -1..1: how many ties one ballot settles;
  3. Proposition 9 on random profiles of weak orders: k times the profile plus any strict ballot has
     a unique maximal lottery for k >= 2, and every even Pfaffian is +-1 modulo k;
  4. two candidates that no ballot distinguishes: cloning one of them changes the shares;
  5. the tie-breaker "random voters in turn, then a random order of the candidates", with the order
     drawn either uniformly or along the tree of clone sets: independence of clones on random
     profiles whenever no outsider is ranked equal to the cloned candidate on every ballot;
  6. six candidates, eight voters: the voters leave open a segment between two lotteries on
     candidates that the ballots do distinguish; with the uniform order the rule is not independent
     of clones there, with the order drawn along the tree of clone sets it is.
Run: python3 equality_equal_rankings.py   (needs numpy and scipy; about three minutes)
"""
import itertools
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


def show(ballot, names="abcdefgh"):
    return " > ".join("=".join(names[x] for x in cl) for cl in classes(ballot))


def read(text, names):
    level = {x: i for i, cl in enumerate(text.split(">")) for x in cl.strip().split("=")}
    return tuple(level[x] for x in names)


# ---------- maximal lotteries ----------

def lp(G, objective, A_eq=None, b_eq=None):
    m = len(G)
    A_eq = [np.ones(m)] if A_eq is None else A_eq
    b_eq = [1.0] if b_eq is None else b_eq
    return linprog(objective, A_ub=-G.T, b_ub=np.zeros(m), A_eq=np.array(A_eq), b_eq=b_eq,
                   bounds=(0, 1), method="highs").x


def unique(G):
    c = rng.normal(size=len(G))
    return np.allclose(lp(G, c), lp(G, -c), atol=1e-7)


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


# ---------- the tree of clone sets ----------

def is_clone_set(profile, X, m):
    """Every outsider is above all of X, below all of X or equal to all of X, on every ballot."""
    return all(len({np.sign(r[y] - r[x]) for x in X}) == 1
               for r in profile for y in range(m) if y not in X)


def tree_orders(profile, m):
    """Random strict order of the candidates drawn along the tree of clone sets: at each node the
    children are put in a uniformly random order, except where they form a line (unions of
    neighbours are clone sets, others are not): there one of the two directions is drawn. Returns
    the orders with their probabilities."""
    everyone = frozenset(range(m))
    family = [frozenset(X) for k in range(2, m) for X in itertools.combinations(range(m), k)
              if is_clone_set(profile, X, m)]
    overlap = lambda X, Y: X & Y and not X <= Y and not Y <= X
    strong = [X for X in family if not any(overlap(X, Y) for Y in family)]
    strong += [frozenset([x]) for x in range(m)]

    def orders(C):
        if len(C) == 1:
            return {tuple(C): 1.0}
        inside = [X for X in strong if X < C]
        children = [X for X in inside if not any(X < Y for Y in inside)]
        assert sum(len(X) for X in children) == len(C)
        k = len(children)
        joined = {(i, j) for i, j in itertools.combinations(range(k), 2)
                  if k > 2 and children[i] | children[j] in family}
        if joined and len(joined) < k * (k - 1) // 2:                # a line
            degree = [sum(i in pair for pair in joined) for i in range(k)]
            line = [degree.index(1)]
            while len(line) < k:
                line.append(next(j for j in range(k) if j not in line
                                 and tuple(sorted((line[-1], j))) in joined))
            arrangements = [tuple(line), tuple(reversed(line))]
        else:
            arrangements = list(itertools.permutations(range(k)))
        out = {}
        for arrangement in arrangements:
            partial = {(): 1.0 / len(arrangements)}
            for i in arrangement:
                partial = {o + o2: w * w2 for o, w in partial.items()
                           for o2, w2 in orders(children[i]).items()}
            for o, w in partial.items():
                out[o] = out.get(o, 0) + w
        return out

    return orders(everyone)


# ---------- the tie-breaker: random voters in turn, then a random order of the candidates ----------

def narrow(G, A_eq, b_eq, class_list):
    """Keep the lotteries that are best for an order of classes: the largest total for the first
    class, then the largest for the second, and so on."""
    A_eq, b_eq = list(A_eq), list(b_eq)
    for cl in class_list:
        e = np.zeros(len(G))
        e[list(cl)] = 1
        A_eq.append(e)
        b_eq.append(lp(G, -e, A_eq[:-1], b_eq) @ e)
    return A_eq, b_eq


def rule(profile, m, last="tree", report=None):
    """Maximal lotteries with ties broken by random voters in turn. A voter whose ballot narrows the
    current set is drawn with probability proportional to the share of that ballot; the others would
    change nothing. What all voters leave open is decided by a random order of the candidates:
    uniform (last="uniform") or drawn along the tree of clone sets (last="tree")."""
    G = margins(profile, m)
    types = {}
    for r in profile:
        types[r] = types.get(r, 0) + 1

    def left_open(A, b):
        low = np.array([lp(G, np.eye(m)[x], A, b)[x] for x in range(m)])
        high = np.array([lp(G, -np.eye(m)[x], A, b)[x] for x in range(m)])
        free = [x for x in range(m) if high[x] - low[x] > 1e-7]
        if not free:
            return lp(G, np.zeros(m), A, b)
        if report is not None:
            report.append((low.round(3), high.round(3)))
        if last == "uniform":
            orders = {o: 1.0 for o in itertools.permutations(free)}
        else:
            orders = {}
            for o, w in tree_orders(profile, m).items():
                key = tuple(x for x in o if x in free)
                orders[key] = orders.get(key, 0) + w
        total = sum(orders.values())
        out = np.zeros(m)
        for o, w in orders.items():
            A2, b2 = narrow(G, A, b, [[x] for x in o])
            out += w / total * lp(G, np.zeros(m), A2, b2)
        return out

    def go(A, b):
        steps = []
        for t, count in types.items():
            A2, b2 = list(A), list(b)
            changed = False
            for cl in classes(t)[:-1]:
                e = np.zeros(m)
                e[cl] = 1
                best = lp(G, -e, A2, b2) @ e
                changed = changed or best - lp(G, e, A2, b2) @ e > 1e-7
                A2.append(e)
                b2.append(best)
            if changed:
                steps.append((count, A2, b2))
        if not steps:
            return left_open(A, b)
        total = sum(count for count, _, _ in steps)
        return sum(count / total * go(A2, b2) for count, A2, b2 in steps)

    return go([np.ones(m)], [1.0])


# ---------- 1. a tie that no single ballot settles ----------
W4 = weak_orders(4)
stuck = [read(t, "abcd") for t in ("a=c > b=d", "b > a > d > c", "d > c > b > a")]
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

# ---------- 3. Proposition 9 ----------
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
before = [read("a=x > z", "axz")]
after = [read("a=x=y > z", "axzy")]                        # y is the clone x'
L, L2 = rule(before, 3), rule(after, 4)
print(f"4. a = x > z: (a, x, z) = {np.abs(L).round(3)}; with x cloned, a = x = x' > z: a {L2[0]:.3f},"
      f" the group x, x' {L2[1] + L2[3]:.3f}")
assert np.isclose(L[1], 0.5) and np.isclose(L2[1] + L2[3], 2 / 3)

# ---------- 5. the tie-breaker under cloning, random profiles ----------
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
    ties = same = 0
    fails = {"uniform": 0, "tree": 0}
    for _ in range(trials):
        prof = [W[i] for i in rng.integers(len(W), size=int(rng.integers(1, 6)))]
        x = int(rng.integers(m))
        cloned = clone(prof, x, m)
        ties += not unique(margins(cloned, m + 1))
        excepted = any(all(r[y] == r[x] for r in prof) for y in range(m) if y != x)
        same += excepted
        for last in ("uniform", "tree"):
            L, L2 = rule(prof, m, last), rule(cloned, m + 1, last)
            merged = L2[:m].copy()
            merged[x] += L2[m]
            if not excepted:
                fails[last] += not np.allclose(merged, L, atol=1e-7)
    print(f"5. {m} candidates, one cloned, {trials} random profiles ({ties} with a tie after cloning, {same} under"
          f" the exception): of the other {trials - same}, not independent of clones:"
          f" {fails['uniform']} with the uniform order, {fails['tree']} with the order along the tree")
    assert fails == {"uniform": 0, "tree": 0}

# ---------- 6. what the voters leave open ----------
names = "abcdeg"
texts = ["g > c=d > e > a=b", "c=d > e > a=b > g", "e=g > a=b > c=d", "a=b > c=d > e=g",
         "e > b=d > g > a=c", "b=d > g > a=c > e", "e=g > a=c > b=d", "a=c > b=d > e=g"]
prof = [read(t, names) for t in texts]
G = margins(prof, 6)
assert not G[:4, :4].any()
print("6. six candidates, eight voters:", "; ".join(texts))
print("   a, b, c, d tie pairwise; e beats a, b and loses to c, d; g beats a, c and loses to b, d")
opened = []
L = {last: rule(prof, 6, last, opened if last == "uniform" else None) for last in ("uniform", "tree")}
low, high = opened[0]
print(f"   left open by the voters: probabilities from {np.abs(low[:4])} to {np.abs(high[:4])} for a, b, c, d")
assert all(np.allclose(lo[:4], 0) and np.allclose(hi[:4], 0.5) for lo, hi in opened)
cloned = [r + (r[0],) for r in prof]                       # a' ranked equal to a on every ballot
for last in ("uniform", "tree"):
    L2 = rule(cloned, 7, last)
    print(f"   {last:7s} order: a {L[last][0]:.4f}, d {L[last][3]:.4f}; after cloning a:"
          f" a and a' together {L2[0] + L2[6]:.4f}, d {L2[3]:.4f}")
    assert np.isclose(L2[0] + L2[6], L[last][0]) == (last == "tree")
print("all checks passed")
