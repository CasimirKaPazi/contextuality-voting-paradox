"""Survey of rules on strict rankings against equality of voters and alternatives (EC-VA).

For each rule, on random profiles of strict rankings:
  A. reversal pairs: at a profile with a single winner, add ballots together with their reverses and
     see whether the winner changes (a rule that depends only on margins cannot change);
  B. clones: replace a candidate by two or three clones, adjacent on every ballot (in random order,
     or three clones in the three orders of a cycle in turn), and see whether the winner stays (or
     stays within the clones), for profiles with a single winner before and after;
  C. for the rules that pass A and B: whether a tie (several winners) in ten copies of a profile can
     be removed by one more ballot. A tie is a tie in every multiple of the electorate, so this is
     what "within a fraction of a vote" asks.
The first counterexample found is printed. Rules with ties in an elimination step return every
candidate that wins for some way of breaking them.
Used in notes/equality-of-voters-and-alternatives.md, Section 4.
Run: python3 equality_rule_survey.py   (needs numpy; about fifteen seconds)
"""
import itertools
from functools import lru_cache
import numpy as np

rng = np.random.default_rng(6)


def margins(profile, m):
    M = np.zeros((m, m), dtype=int)
    for r in profile:
        for i, x in enumerate(r):
            for y in r[i + 1:]:
                M[x, y] += 1
                M[y, x] -= 1
    return M


def best(score):
    top = max(score.values())
    return frozenset(x for x, v in score.items() if v == top)


def borda_scores(profile, alive):
    score = {x: 0 for x in alive}
    for r in profile:
        rest = [x for x in r if x in alive]
        for i, x in enumerate(rest):
            score[x] += len(rest) - 1 - i
    return score


# ---------- positional and elimination rules ----------

def plurality(profile, m):
    return best({x: sum(r[0] == x for r in profile) for x in range(m)})


def antiplurality(profile, m):
    return best({x: -sum(r[-1] == x for r in profile) for x in range(m)})


def borda(profile, m):
    return best(borda_scores(profile, range(m)))


def bucklin(profile, m):
    for k in range(1, m + 1):
        count = {x: sum(x in r[:k] for r in profile) for x in range(m)}
        if max(count.values()) * 2 > len(profile):
            return best(count)


def eliminate(profile, m, loser_scores):
    """Remove a candidate with the lowest score until one is left; every way of breaking ties."""
    @lru_cache(maxsize=None)
    def go(alive):
        if len(alive) == 1:
            return alive
        score = loser_scores(profile, alive)
        low = min(score.values())
        out = frozenset()
        for x in alive:
            if score[x] == low:
                out |= go(alive - {x})
        return out
    return go(frozenset(range(m)))


def instant_runoff(profile, m):
    firsts = lambda prof, alive: {x: sum(next(y for y in r if y in alive) == x for r in prof) for x in alive}
    return eliminate(profile, m, firsts)


def coombs(profile, m):
    lasts = lambda prof, alive: {x: -sum(next(y for y in reversed(r) if y in alive) == x for r in prof)
                                 for x in alive}
    return eliminate(profile, m, lasts)


def baldwin(profile, m):
    return eliminate(profile, m, borda_scores)


def nanson(profile, m):
    alive = set(range(m))
    while True:
        score = borda_scores(profile, alive)
        mean = sum(score.values()) / len(alive)
        keep = {x for x in alive if score[x] > mean}
        if not keep or keep == alive:
            return frozenset(alive)
        alive = keep


# ---------- rules that depend on the margins ----------

def copeland(profile, m):
    M = margins(profile, m)
    return best({x: int(np.sign(M[x]).sum()) for x in range(m)})


def minimax(profile, m):
    M = margins(profile, m)
    return best({x: -max(M[y, x] for y in range(m) if y != x) for x in range(m)})


def black(profile, m):
    M = margins(profile, m)
    for x in range(m):
        if all(M[x, y] > 0 for y in range(m) if y != x):
            return frozenset([x])
    return borda(profile, m)


def kemeny(profile, m):
    M = margins(profile, m)
    score = {r: sum(M[r[i], r[j]] for i in range(m) for j in range(i + 1, m))
             for r in itertools.permutations(range(m))}
    top = max(score.values())
    return frozenset(r[0] for r, v in score.items() if v == top)


def strongest_paths(M, links):
    m = len(M)
    P = np.where(links, M, -np.inf).astype(float)
    for k in range(m):
        for i in range(m):
            for j in range(m):
                if i != j:
                    P[i, j] = max(P[i, j], min(P[i, k], P[k, j]))
    return P


def split_cycle(profile, m):
    """x defeats y if x beats y by more than the strength of the strongest path from y back to x."""
    M = margins(profile, m)
    P = strongest_paths(M, M > 0)
    return frozenset(y for y in range(m)
                     if not any(M[x, y] > 0 and M[x, y] > P[y, x] for x in range(m) if x != y))


def schulze(profile, m):
    M = margins(profile, m)
    P = strongest_paths(M, ~np.eye(m, dtype=bool))
    return frozenset(x for x in range(m) if all(P[x, y] >= P[y, x] for y in range(m) if y != x))


def ranked_pairs(profile, m):
    """Winners over all ways of ordering pairs of equal strength (Tideman 1987)."""
    M = margins(profile, m)
    strengths = sorted({M[x, y] for x in range(m) for y in range(m) if x != y and M[x, y] >= 0}, reverse=True)
    groups = [frozenset((x, y) for x in range(m) for y in range(m) if x != y and M[x, y] == s)
              for s in strengths]

    def reaches(locked, x, y):
        seen, todo = {x}, [x]
        while todo:
            u = todo.pop()
            for (s, t) in locked:
                if s == u and t not in seen:
                    seen.add(t)
                    todo.append(t)
        return y in seen

    @lru_cache(maxsize=None)
    def go(locked, gi, remaining):
        if not remaining:
            if gi + 1 == len(groups):
                return frozenset(x for x in range(m) if all(t != x for (_, t) in locked))
            return go(locked, gi + 1, groups[gi + 1])
        out = frozenset()
        for (x, y) in remaining:
            new = locked if reaches(locked, y, x) else locked | {(x, y)}
            out |= go(new, gi, remaining - {(x, y)})
        return out

    return go(frozenset(), 0, groups[0])


RULES = [("plurality", plurality), ("antiplurality", antiplurality), ("Borda", borda), ("Bucklin", bucklin),
         ("instant runoff", instant_runoff), ("Coombs", coombs), ("Baldwin", baldwin), ("Nanson", nanson),
         ("Black", black), ("Copeland", copeland), ("minimax", minimax), ("Kemeny", kemeny),
         ("Split Cycle", split_cycle), ("ranked pairs", ranked_pairs), ("Schulze", schulze)]


# ---------- profiles ----------

def random_profile(m, n):
    ranks = list(itertools.permutations(range(m)))
    return [ranks[i] for i in rng.integers(len(ranks), size=n)]


def clone(profile, x, m, extra, cycle=False):
    """Replace x by x and `extra` further clones (numbered m, m+1, ...): in random order on each
    ballot, or (three clones) in the three orders of a cycle, ballot by ballot in turn."""
    out = []
    for n, r in enumerate(sorted(profile)):
        i, group = r.index(x), [x] + list(range(m, m + extra))
        if cycle:
            group = group[n % 3:] + group[:n % 3]
        else:
            rng.shuffle(group)
        out.append(r[:i] + tuple(int(g) for g in group) + r[i + 1:])
    return out


def show(profile, names="abcdef"):
    kinds = {}
    for r in profile:
        kinds[r] = kinds.get(r, 0) + 1
    return ", ".join(f"{c} {''.join(names[x] for x in r)}" for r, c in sorted(kinds.items()))


# ---------- A and B ----------
print("A: reversal pairs change a single winner.  B: clones change a single winner.")
passed = []
for name, rule in RULES:
    a_cases = a_fail = b_cases = b_fail = 0
    a_example = b_example = None
    for _ in range(600):
        m = int(rng.choice([3, 4]))
        prof = random_profile(m, int(rng.integers(3, 12)))
        w = rule(tuple(prof), m)
        if len(w) != 1:
            continue
        pairs = []
        for _ in range(int(rng.integers(1, 4))):
            b = random_profile(m, 1)[0]
            pairs += [b, tuple(reversed(b))]
        a_cases += 1
        if rule(tuple(prof + pairs), m) != w:
            a_fail += 1
            a_example = a_example or f"{show(prof)}; added {show(pairs)}"
        x, extra = int(rng.integers(m)), int(rng.choice([1, 2]))
        cloned = clone(prof, x, m, extra, cycle=extra == 2 and rng.random() < 0.5)
        w2 = rule(tuple(cloned), m + extra)
        if len(w2) == 1:
            b_cases += 1
            if frozenset(x if y >= m else y for y in w2) != w:
                b_fail += 1
                b_example = b_example or f"{show(prof)}; {'abcd'[x]} cloned: {show(cloned)}"
    print(f"{name:15s} A: {a_fail:3d} of {a_cases}   B: {b_fail:3d} of {b_cases}")
    if a_example:
        print(f"                A, first case: {a_example}")
    if b_example:
        print(f"                B, first case: {b_example}")
    if not a_fail and not b_fail:
        passed.append((name, rule))
print("pass A and B:", ", ".join(name for name, _ in passed))

# ---------- C: ties ----------
ballots4 = list(itertools.permutations(range(4)))
for name, rule in passed:
    ties = stay = 0
    example = None
    for _ in range(300):
        prof = random_profile(4, int(rng.integers(3, 10)))
        if len(rule(tuple(prof), 4)) > 1:
            ties += 1
            if not any(len(rule(tuple(prof * 10 + [r]), 4)) == 1 for r in ballots4):
                stay += 1
                example = example or prof
    print(f"C: {name}: {ties} ties among 300 profiles of four candidates; {stay} not removed by any ballot"
          " added to ten copies")
    if example:
        M = margins(example, 4)
        print(f"   first case: {show(example)}; margins (ab, ac, ad, bc, bd, cd) ="
              f" {[int(M[i, j]) for i, j in itertools.combinations(range(4), 2)]},"
              f" winners {''.join('abcd'[x] for x in sorted(rule(tuple(example), 4)))}")

# ---------- Split Cycle: a tie that no vote removes ----------
def from_margins(upper, m=4):
    """A profile with the given even margins (McGarvey): two ballots for each margin of 2."""
    prof = []
    for (x, y), v in zip(itertools.combinations(range(m), 2), upper):
        if v < 0:
            x, y, v = y, x, -v
        rest = [z for z in range(m) if z not in (x, y)]
        prof += [(x, y, *rest), (*reversed(rest), x, y)] * (v // 2)
    return prof

example = from_margins([10, -6, 2, 10, -2, -6])            # ab, ac, ad, bc, bd, cd
assert split_cycle(tuple(example), 4) == {0, 3}
for k in (1, 10, 100):
    assert all(split_cycle(tuple(example * k + [r]), 4) == {0, 3} for r in ballots4)
print("Split Cycle, margins a>b 10, b>c 10, c>a 6, d>c 6, a>d 2, d>b 2: winners a and d, also in 1, 10 and"
      " 100 copies with any ballot added;")
print(f"   ranked pairs elects {''.join('abcd'[x] for x in ranked_pairs(tuple(example), 4))},"
      f" Schulze {''.join('abcd'[x] for x in schulze(tuple(example), 4))}")

# ---------- Split Cycle contains ranked pairs and Schulze ----------
inside = 0
for _ in range(400):
    m = int(rng.choice([3, 4]))
    prof = tuple(random_profile(m, int(rng.integers(3, 10))))
    sc = split_cycle(prof, m)
    assert ranked_pairs(prof, m) <= sc and schulze(prof, m) <= sc
    inside += 1
print(f"the winners of ranked pairs and of Schulze are among the Split Cycle winners in all {inside} profiles")
