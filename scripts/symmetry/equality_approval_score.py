"""Approval and score voting against equality of voters and alternatives (EC-VA).

Checks Section 7 of notes/equality-of-voters-and-alternatives.md. A ballot gives every candidate a
score from 0 to K (K = 1 is approval); its reverse gives K minus the score. The winners are the
candidates with the largest total. Two tie-breakers:
  - random voters in turn: each narrows the tied candidates to those the voter scores highest, and
    what is left when every ballot has been drawn is divided equally;
  - the uniform lottery over the tied winners.
Checks, on random profiles with K = 1, 2, 5 and three or four candidates:
  1. a ballot and its reverse never change a unique winner (the profile is settled);
  2. every tie is within one vote: one ballot for one of the tied candidates gives a unique winner;
  3. clones with the same score on every ballot: with random voters in turn the rule is independent
     of clones whenever no outsider has the same scores as the cloned candidate on every ballot;
     with the uniform tie-breaker it is not;
  4. clones that are only adjacent in the order of every ballot: score voting is not independent;
  5. STAR (the two largest totals, then the majority between them) is not independent of clones;
  6. BTR-score (candidates in the order of their totals; the two lowest are compared pairwise, the
     winner meets the next one up, a pairwise tie goes to the higher one; ties in the totals ordered
     by random voters in turn): profiles whose outcome does not depend on the order of tied totals
     stay so under reversal pairs; every tie is within one vote, also with more candidates than
     score levels and all totals equal; K + 1 copies of any profile plus the ballot of the kings
     (Proposition 12) are decided; independent of clones with the same scores.
Run: python3 equality_approval_score.py   (needs numpy; a few seconds)
"""
import itertools
import numpy as np

rng = np.random.default_rng(4)


def totals(profile, m):
    return np.sum(profile, axis=0) if len(profile) else np.zeros(m)


def winners(profile, m):
    t = totals(profile, m)
    return [x for x in range(m) if t[x] == t.max()]


def voters_in_turn(profile, m):
    """Lottery of score voting with ties broken by random voters in turn. The next new ballot is t
    with probability share(t) / (share of the ballots not yet drawn)."""
    types = {}
    for r in profile:
        types[tuple(r)] = types.get(tuple(r), 0) + 1

    def go(tied, left):
        out = np.zeros(m)
        if len(tied) == 1 or not left:
            out[list(tied)] = 1 / len(tied)
            return out
        total = sum(left.values())
        for t, count in left.items():
            top = max(t[x] for x in tied)
            rest = {u: v for u, v in left.items() if u != t}
            out += count / total * go(tuple(x for x in tied if t[x] == top), rest)
        return out

    return go(tuple(winners(profile, m)), types)


def uniform(profile, m):
    out = np.zeros(m)
    w = winners(profile, m)
    out[w] = 1 / len(w)
    return out


def random_profile(m, K, n):
    return [tuple(int(s) for s in rng.integers(0, K + 1, size=m)) for _ in range(n)]


def reverse(ballot, K):
    return tuple(K - s for s in ballot)


for K in (1, 2, 5):
    settled = ties = clone_cases = same = same_fail = uniform_fail = 0
    for m in (3, 4):
        for _ in range(1500):
            prof = random_profile(m, K, int(rng.integers(1, 7)))
            w = winners(prof, m)
            # 1. settled where the winner is unique
            if len(w) == 1:
                settled += 1
                extra = []
                for _ in range(int(rng.integers(1, 4))):
                    b = random_profile(m, K, 1)[0]
                    extra += [b, reverse(b, K)]
                assert winners(prof + extra, m) == w
            # 2. ties within one vote
            else:
                ties += 1
                for x in w:
                    assert winners(prof + [tuple(K if y == x else 0 for y in range(m))], m) == [x]
            # 3. clones with the same score on every ballot
            x = int(rng.integers(m))
            cloned = [r + (r[x],) for r in prof]
            for rule in (voters_in_turn, uniform):
                L, L2 = rule(prof, m), rule(cloned, m + 1)
                merged = L2[:m].copy()
                merged[x] += L2[m]
                ok = np.allclose(merged, L)
                excepted = any(all(r[y] == r[x] for r in prof) for y in range(m) if y != x)
                if rule is uniform:
                    uniform_fail += not ok and not excepted
                elif excepted:
                    same += 1
                    same_fail += not ok
                else:
                    clone_cases += 1
                    assert ok
    name = "approval" if K == 1 else f"scores 0..{K}"
    print(f"{name}: {settled} profiles with a unique winner, all settled; {ties} ties, all within one vote;")
    print(f"   random voters in turn: independent of clones in all {clone_cases} cases where some ballot"
          f" separates every outsider from the cloned candidate ({same_fail} of the other {same} fail);")
    print(f"   uniform tie-breaker: fails in {uniform_fail} of the same {clone_cases} cases")

# 4. clones that are only adjacent in every ballot's order: candidates a, x, then x'
before = [(5, 1)] * 3 + [(0, 5)] * 2
after = [(5, 1, 4)] * 3 + [(0, 5, 5)] * 2
assert winners(before, 2) == [0] and winners(after, 3) == [2]
print(f"4. scores 0..5: totals (a, x) = {totals(before, 2).tolist()}, a wins; with x' placed next to x on"
      f" every ballot, totals (a, x, x') = {totals(after, 3).tolist()}, x' wins")

# 5. STAR: the two largest totals, then the majority between them
def star(profile, m):
    t = totals(profile, m)
    order = sorted(range(m), key=lambda y: -t[y])
    assert m == 2 or t[order[1]] > t[order[2]]              # the example has no tie for the runoff
    x, y = order[:2]
    pref = sum((r[x] > r[y]) - (r[x] < r[y]) for r in profile)
    return {x} if pref > 0 else {y} if pref < 0 else {x, y}

before = [(1, 0, 0)] * 3 + [(0, 5, 1)] * 2                # candidates a, x, b
after = [(1, 0, 0, 0)] * 3 + [(0, 5, 1, 5)] * 2           # x' = last, same scores as x
assert star(before, 3) == {0} and star(after, 4) == {1, 3}
print("5. STAR: a wins the runoff against x; with x cloned (same scores), x and x' fill the runoff")
# 6. BTR-score
def margin(profile, x, y):
    return sum((r[x] > r[y]) - (r[x] < r[y]) for r in profile)


def btr(order, profile):
    """order: the candidates from the largest total to the smallest."""
    current = order[-1]
    for higher in reversed(order[:-1]):
        if margin(profile, current, higher) <= 0:          # the higher one wins unless strictly beaten
            current = higher
    return current


def tied_groups(profile, m):
    t = totals(profile, m)
    return [tuple(x for x in range(m) if t[x] == v) for v in sorted(set(t.tolist()), reverse=True)]


def linear_orders(groups):
    for parts in itertools.product(*[itertools.permutations(g) for g in groups]):
        yield tuple(x for part in parts for x in part)


def possible(profile, m):
    """The winners over all ways of ordering candidates with equal totals."""
    return {btr(order, profile) for order in linear_orders(tied_groups(profile, m))}


def btr_rule(profile, m):
    """Ties in the totals: random voters in turn put tied candidates in the order of their scores;
    candidates that no ballot separates are ordered at random."""
    types = {}
    for r in profile:
        types[r] = types.get(r, 0) + 1

    def go(groups, left):
        out = np.zeros(m)
        if all(len(g) == 1 for g in groups) or not left:
            orders = list(linear_orders(groups))
            for order in orders:
                out[btr(order, profile)] += 1 / len(orders)
            return out
        total = sum(left.values())
        for t, count in left.items():
            finer = [tuple(x for x in g if t[x] == v) for g in groups
                     for v in sorted({t[x] for x in g}, reverse=True)]
            out += count / total * go(finer, {u: v for u, v in left.items() if u != t})
        return out

    return go(tied_groups(profile, m), types)


for K, m, trials in [(1, 3, 300), (2, 3, 300), (2, 4, 300), (5, 4, 300)]:
    ballots = list(itertools.product(range(K + 1), repeat=m))
    decided = ties = clone_cases = 0
    for _ in range(trials):
        prof = random_profile(m, K, int(rng.integers(1, 6)))
        w = possible(prof, m)
        if len(w) == 1:
            decided += 1
            extra = []
            for _ in range(int(rng.integers(1, 4))):
                b = random_profile(m, K, 1)[0]
                extra += [b, reverse(b, K)]
            assert possible(prof + extra, m) == w
        else:
            ties += 1
            assert any(len(possible(prof + [r], m)) == 1 for r in ballots)
        x = int(rng.integers(m))
        cloned = [r + (r[x],) for r in prof]
        L, L2 = btr_rule(prof, m), btr_rule(cloned, m + 1)
        merged = L2[:m].copy()
        merged[x] += L2[m]
        if not any(all(r[y] == r[x] for r in prof) for y in range(m) if y != x):
            clone_cases += 1
            assert np.allclose(merged, L)
    print(f"6. BTR-score, scores 0..{K}, {m} candidates: {decided} decided profiles stay decided under reversal"
          f" pairs; {ties} ties, all within one vote; independent of clones in all {clone_cases} cases"
          f" outside the exception")
for K, m, trials in [(2, 4, 150), (2, 5, 100), (2, 6, 30)]:   # more candidates than levels, all totals equal
    ballots = list(itertools.product(range(K + 1), repeat=m))
    ties = 0
    for _ in range(trials):
        prof = []
        for _ in range(int(rng.integers(1, 4))):
            b = random_profile(m, K, 1)[0]
            prof += [b[i:] + b[:i] for i in range(m)]
        assert len(set(totals(prof, m).tolist())) == 1
        if len(possible(prof, m)) > 1:
            ties += 1
            assert any(len(possible(prof + [r], m)) == 1 for r in ballots)
    print(f"   scores 0..{K}, {m} candidates, all totals equal: {ties} ties of {trials} profiles, all within one vote")


def king_ballot(profile, m):
    """In every group of candidates with equal totals: 2 for a member that as many members as
    possible do not beat (a king), 1 for the members that do not beat it, 0 for those that do."""
    ballot = [0] * m
    for group in tied_groups(profile, m):
        king = max(group, key=lambda x: sum(margin(profile, y, x) <= 0 for y in group))
        for x in group:
            ballot[x] = 2 if x == king else 1 if margin(profile, x, king) <= 0 else 0
    return tuple(ballot)


for K, m, trials in [(2, 4, 300), (2, 5, 300), (2, 6, 100), (5, 5, 200)]:
    ties = 0
    for _ in range(trials):
        prof = random_profile(m, K, int(rng.integers(1, 6)))
        if rng.random() < 0.5:                              # many equal totals
            b = prof[0]
            prof = [b[i:] + b[:i] for i in range(m)] + prof[1:] + [reverse(r, K) for r in prof[1:]]
        ties += len(possible(prof, m)) > 1
        assert len(possible(prof * (K + 1) + [king_ballot(prof, m)], m)) == 1
    print(f"   scores 0..{K}, {m} candidates: K + 1 copies plus the ballot of the kings are decided in all"
          f" {trials} profiles ({ties} ties)")

# seven candidates, scores 0..2, all totals equal, pairwise comparisons of the Paley tournament
m = 7
paley = [tuple(2 if y == x else 1 if (y - x) % 7 in (1, 2, 4) else 0 for y in range(7)) for x in range(7)]
M0 = np.array([[margin(paley, x, y) for y in range(m)] for x in range(m)])
assert len(set(totals(paley, m).tolist())) == 1 and (M0 == 0).sum() == m


def decided_after(ballot, copies=3):
    """Is the outcome of `copies` copies of the profile plus the ballot independent of the order of
    equal totals? With all totals equal the candidates are ordered by the ballot's scores."""
    add = np.array(ballot)
    M = copies * M0 + np.sign(add[:, None] - add[None, :])
    groups = [tuple(x for x in range(m) if ballot[x] == v) for v in sorted(set(ballot), reverse=True)]
    seen = set()
    for order in linear_orders(groups):
        current = order[-1]
        for higher in reversed(order[:-1]):
            if M[current, higher] <= 0:
                current = higher
        seen.add(current)
        if len(seen) > 1:
            return False
    return True


two_levels = [b for b in itertools.product((0, 2), repeat=m) if decided_after(b)]
three_levels = next(b for b in itertools.product(range(3), repeat=m) if decided_after(b))
print(f"   seven candidates, Paley tournament, all totals equal: no ballot with two levels settles three copies"
      f" ({len(two_levels)} of 128), the ballot {three_levels} does")
assert not two_levels
print("all checks passed")
