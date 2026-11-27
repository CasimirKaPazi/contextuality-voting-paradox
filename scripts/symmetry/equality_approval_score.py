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
  5. STAR (the two largest totals, then the majority between them) is not independent of clones.
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
print("all checks passed")
