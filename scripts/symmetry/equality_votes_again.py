"""The tie-breaker "the voters vote again", for rankings with equal ranks (Proposition 16).

Voters are drawn until every ballot has come up; the first new ballot is added to the profile with
an infinitesimal weight, the second with a weight infinitesimal against the first, and so on; last
comes a strict order of the candidates drawn along the tree of clone sets, with the smallest
weight. The outcome is the maximal lottery of the profile so perturbed. It is computed exactly:
margins are polynomials in the infinitesimals, the sign of a polynomial is that of its leading term,
and the lottery is read off from the Pfaffians (Proposition 8).

Checks:
  1. on strict rankings the rule is the third rule of Proposition 15 (first voter only);
  2. on random profiles with equal ranks it gives a maximal lottery and is independent of clones
     whenever no outsider is ranked equal to the cloned candidate on every ballot.
The six-candidate profile of Section 6, with eight different ballots, is beyond this script.
Run: python3 equality_votes_again.py   (needs numpy and scipy for the comparisons; a few seconds)
"""
import itertools
from fractions import Fraction
import numpy as np
from scipy.optimize import linprog

rng = np.random.default_rng(21)


# ---------- polynomials in infinitesimals e_1 >> e_2 >> ... : dict {exponents: coefficient} ----------

def p_add(a, b, sign=1):
    out = dict(a)
    for k, v in b.items():
        out[k] = out.get(k, 0) + sign * v
        if out[k] == 0:
            del out[k]
    return out


def p_mul(a, b):
    out = {}
    for k1, v1 in a.items():
        for k2, v2 in b.items():
            k = tuple(x + y for x, y in zip(k1, k2))
            out[k] = out.get(k, 0) + v1 * v2
            if out[k] == 0:
                del out[k]
    return out


def leading(a):
    """The leading term as all infinitesimals tend to zero, each infinitely faster than the one
    before: least power of the last, then of the one before, and so on."""
    key = min(a, key=lambda k: tuple(reversed(k)))
    return key, a[key]


def pfaffian(M, idx):
    if not idx:
        return {(0,) * NVARS: 1}
    first, total = idx[0], {}
    for j in range(1, len(idx)):
        entry = M[first][idx[j]]
        if entry:
            rest = idx[1:j] + idx[j + 1:]
            total = p_add(total, p_mul(entry, pfaffian(M, rest)), 1 if j % 2 else -1)
    return total


def exact_lottery(M, m):
    """The unique maximal lottery of the perturbed margins M in the limit, or None if a tie remains."""
    for size in range(1, m + 1, 2):
        for E in itertools.combinations(range(m), size):
            v = [pfaffian(M, E[:j] + E[j + 1:]) for j in range(size)]
            if not all(v):
                continue
            lead = [leading(x) for x in v]
            signs = {(1 if c > 0 else -1) * (-1) ** j for j, (_, c) in enumerate(lead)}
            if len(signs) != 1:
                continue
            sign = signs.pop()
            outside = [pfaffian(M, E + (y,)) for y in range(m) if y not in E]
            if not all(o and (leading(o)[1] > 0) == (sign > 0) for o in outside):
                continue
            best = min((k for k, _ in lead), key=lambda k: tuple(reversed(k)))
            total = sum(c * (-1) ** j for j, (k, c) in enumerate(lead) if k == best)
            out = np.zeros(m)
            for j, (k, c) in enumerate(lead):
                if k == best:
                    out[E[j]] = float(Fraction(c * (-1) ** j, total))
            return out
    return None


def ballot_margins(ballot):
    m = len(ballot)
    return [[(ballot[y] > ballot[x]) - (ballot[y] < ballot[x]) for y in range(m)] for x in range(m)]


def perturbed(profile, m, added):
    """Margins of the profile plus the added ballots, the i-th with weight e_i."""
    M = [[{} for _ in range(m)] for _ in range(m)]
    zero = (0,) * NVARS
    for r in profile:
        B = ballot_margins(r)
        for x in range(m):
            for y in range(m):
                if B[x][y]:
                    M[x][y] = p_add(M[x][y], {zero: B[x][y]})
    for i, r in enumerate(added):
        key = tuple(int(j == i) for j in range(NVARS))
        B = ballot_margins(r)
        for x in range(m):
            for y in range(m):
                if B[x][y]:
                    M[x][y] = p_add(M[x][y], {key: B[x][y]})
    return M


# ---------- the tree of clone sets (as in equality_equal_rankings.py) ----------

def is_clone_set(profile, X, m):
    return all(len({np.sign(r[y] - r[x]) for x in X}) == 1 for r in profile for y in range(m) if y not in X)


def tree_orders(profile, m):
    family = [frozenset(X) for k in range(2, m) for X in itertools.combinations(range(m), k)
              if is_clone_set(profile, X, m)]
    overlap = lambda X, Y: X & Y and not X <= Y and not Y <= X
    strong = [X for X in family if not any(overlap(X, Y) for Y in family)] + [frozenset([x]) for x in range(m)]

    def orders(C):
        if len(C) == 1:
            return {tuple(C): 1.0}
        inside = [X for X in strong if X < C]
        children = [X for X in inside if not any(X < Y for Y in inside)]
        k = len(children)
        joined = {(i, j) for i, j in itertools.combinations(range(k), 2)
                  if k > 2 and children[i] | children[j] in family}
        if joined and len(joined) < k * (k - 1) // 2:
            degree = [sum(i in pair for pair in joined) for i in range(k)]
            line = [degree.index(1)]
            while len(line) < k:
                line.append(next(j for j in range(k) if j not in line and tuple(sorted((line[-1], j))) in joined))
            arrangements = [tuple(line), tuple(reversed(line))]
        else:
            arrangements = list(itertools.permutations(range(k)))
        out = {}
        for arrangement in arrangements:
            partial = {(): 1.0 / len(arrangements)}
            for i in arrangement:
                partial = {o + o2: w * w2 for o, w in partial.items() for o2, w2 in orders(children[i]).items()}
            for o, w in partial.items():
                out[o] = out.get(o, 0) + w
        return out

    return orders(frozenset(range(m)))


# ---------- the rule ----------

def votes_again(profile, m):
    global NVARS
    types = {}
    for r in profile:
        types[r] = types.get(r, 0) + 1
    NVARS = len(types) + 1
    orders = None

    def go(added, left):
        nonlocal orders
        found = exact_lottery(perturbed(profile, m, added), m)
        if found is not None:
            return found
        if not left:
            if orders is None:
                orders = tree_orders(profile, m)
            out = np.zeros(m)
            for order, w in orders.items():
                strict = tuple(order.index(x) for x in range(m))
                out += w * exact_lottery(perturbed(profile, m, added + [strict]), m)
            return out
        total = sum(left.values())
        return sum(count / total * go(added + [t], {u: v for u, v in left.items() if u != t})
                   for t, count in left.items())

    return go([], types)


# ---------- comparisons ----------

def float_margins(profile, m):
    return np.array(sum(np.array(ballot_margins(r)) for r in profile), dtype=float)


def lottery(G):
    m = len(G)
    return linprog(np.zeros(m), A_ub=-G.T, b_ub=np.zeros(m), A_eq=np.ones((1, m)), b_eq=[1],
                   bounds=(0, 1), method="highs").x


def weak_orders(m):
    return [t for t in itertools.product(range(m), repeat=m) if set(t) == set(range(max(t) + 1))]


def canonical(levels):
    vals = sorted(set(levels))
    return tuple(vals.index(v) for v in levels)


def clone(profile, x, m):
    out = []
    for r in profile:
        shared = any(r[y] == r[x] for y in range(m) if y != x)
        level = r[x] if shared or rng.random() < 0.4 else r[x] + rng.choice([-0.5, 0.5])
        out.append(canonical(list(r) + [level]))
    return out


# 1. strict rankings: the third rule of Proposition 15
for m, trials in [(3, 60), (4, 40)]:
    strict = [r for r in weak_orders(m) if max(r) == m - 1]
    for _ in range(trials):
        prof = [strict[i] for i in rng.integers(len(strict), size=int(rng.choice([2, 4])))]
        G = float_margins(prof, m)
        limit = sum(prof.count(r) / len(prof) * lottery(10 ** 5 * G + float_margins([r], m)) for r in set(prof))
        assert np.allclose(votes_again(prof, m), limit, atol=1e-3)
print("1. strict rankings: the rule is that of Proposition 15 (b) on 100 random profiles")

# 2. equal ranks: independence of clones
for m, trials in [(3, 600), (4, 300), (5, 40)]:
    W = weak_orders(m)
    ties = same = 0
    for _ in range(trials):
        prof = [W[i] for i in rng.integers(len(W), size=int(rng.integers(1, 6)))]
        x = int(rng.integers(m))
        cloned = clone(prof, x, m)
        L = votes_again(prof, m)
        assert np.all(L @ float_margins(prof, m) >= -1e-9) and abs(L.sum() - 1) < 1e-9
        ties += exact_lottery(perturbed(prof, m, []), m) is None
        if any(all(r[y] == r[x] for r in prof) for y in range(m) if y != x):
            same += 1
            continue
        L2 = votes_again(cloned, m + 1)
        merged = L2[:m].copy()
        merged[x] += L2[m]
        assert np.allclose(merged, L, atol=1e-9), (prof, x, cloned, L, L2)
    print(f"2. {m} candidates with equal ranks, {trials} random profiles ({ties} ties, {same} under the exception):"
          f" independent of clones in the other {trials - same}")
print("all checks passed")
