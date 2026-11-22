"""Where the twist sits along a profile path (Cycles and Twists, Section 5, three alternatives).

All voters start at a ranking r and switch to its reverse -r one at a time, each through the three
adjacent transpositions that lead half way around the hexagon of strict orders.
Part 1: a dictatorship's social ranking changes only during the dictator's switch, and then all three
        comparisons flip.
Part 2: for a mixture of dictatorships with random weights, the probability of each comparison falls
        from 1 to 0; all three pass 1/2 during the switch of the same voter, the weighted median of the
        switching order, and the lottery there is within one voter's weight of the even mixture of r and
        -r, which reversal fixes.
Part 3: starting from a profile that is not unanimous, the three comparisons pass 1/2 at different
        voters in many cases.
Plain Python 3; run: python3 pivotal_path.py
"""
import itertools
import random

random.seed(3)
PAIRS = [(0, 1), (1, 2), (0, 2)]


def above(rank, x, y):
    return rank.index(x) < rank.index(y)


def half_turn(r):
    """r, then three adjacent transpositions, ending at the reverse of r."""
    path = [tuple(r)]
    cur = list(r)
    for i in (0, 1, 0):
        cur[i], cur[i + 1] = cur[i + 1], cur[i]
        path.append(tuple(cur))
    assert path[-1] == tuple(reversed(r))
    return path


def profile_path(start):
    """Sequence of (voter switching, profile) as voters switch in order, each through its half turn."""
    prof = [tuple(s) for s in start]
    out = [(None, list(prof))]
    for k in range(len(prof)):
        for step in half_turn(prof[k])[1:]:
            prof[k] = step
            out.append((k, list(prof)))
    return out


def pair_prob(prof, lam, x, y):
    return sum(l for l, rk in zip(lam, prof) if above(rk, x, y))


def part1(trials=200):
    bad = 0
    for _ in range(trials):
        n = random.randint(2, 6); d = random.randrange(n); r = random.sample(range(3), 3)
        path = profile_path([r] * n)
        social = [prof[d] for _, prof in path]
        changes = [path[t][0] for t in range(1, len(path)) if social[t] != social[t - 1]]
        bad += any(k != d for k in changes) or social[-1] != tuple(reversed(r))
    print(f"Part 1: dictatorship changes only during the dictator's switch, ending at the reverse: "
          f"fails in {bad} of {trials}")


def part2(trials=500):
    bad_median = bad_mid = 0
    for _ in range(trials):
        n = random.randint(2, 8); lam = [random.random() for _ in range(n)]; s = sum(lam)
        lam = [l / s for l in lam]; r = random.sample(range(3), 3)
        path = profile_path([r] * n)
        cum = 0; median = None
        for k in range(n):
            cum += lam[k]
            if cum >= 0.5: median = k; break
        for x, y in PAIRS:
            if not above(r, x, y): x, y = y, x
            probs = [pair_prob(prof, lam, x, y) for _, prof in path]
            cross = next(path[t][0] for t in range(1, len(path)) if probs[t] <= 0.5 < probs[t - 1] or probs[t] < 0.5 <= probs[t - 1])
            bad_median += cross != median
        # the lottery when the median voter is half way: distance to the even mixture of r and -r
        t = max(i for i, (k, _) in enumerate(path) if k is not None and k < median) if median > 0 else 0
        prof = path[t][1]
        lot = {}
        for l, rk in zip(lam, prof): lot[rk] = lot.get(rk, 0) + l
        even = {tuple(r): 0.5, tuple(reversed(r)): 0.5}
        dist = sum(abs(lot.get(k, 0) - even.get(k, 0)) for k in set(lot) | set(even)) / 2
        bad_mid += dist > lam[median] + 1e-12
    print(f"Part 2: all three comparisons pass 1/2 during the median voter's switch: fails in {bad_median} "
          f"of {3 * trials} pairs; lottery before that switch within the median's weight of the even "
          f"mixture of r and -r: fails in {bad_mid} of {trials}")


def part3(trials=500):
    differ = 0
    for _ in range(trials):
        n = random.randint(3, 8); lam = [1 / n] * n
        start = [random.sample(range(3), 3) for _ in range(n)]
        path = profile_path(start)
        crossers = set()
        for x, y in PAIRS:
            probs = [pair_prob(prof, lam, x, y) for _, prof in path]
            for t in range(1, len(path)):
                if (probs[t] - 0.5) * (probs[t - 1] - 0.5) < 0 or (probs[t] == 0.5 != probs[t - 1]):
                    crossers.add(path[t][0]); break
        differ += len(crossers) > 1
    print(f"Part 3: non-unanimous start, equal weights: the comparisons pass 1/2 at different voters "
          f"in {differ} of {trials} profiles")


if __name__ == "__main__":
    part1(); part2(); part3()
