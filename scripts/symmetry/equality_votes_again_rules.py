"""The tie-breaker "the voters vote again" for rules that only compare sums (Proposition 18).

A rule that only compares totals or margins can be applied to the profile with the drawn ballots
added at infinitesimal weights without taking a limit: every total or margin becomes a vector
(value in the profile, value on the first added ballot, on the second, ...), and vectors are compared
in lexicographic order.

  1. score voting: this is the tie-breaker "random voters in turn" of Section 7;
  2. ranked pairs and the Schulze method on rankings with equal ranks, with an order of the candidates
     drawn along the tree of clone sets as the last ballot: independence of clones on random profiles
     outside the exception. For ranked pairs, pairs with equal lists are ordered by the last ballot
     (Proposition 19); locked in every order they can leave two winners. For Schulze, of several
     winners at the end the one highest in the last ballot is elected (Proposition 20); sharing
     equally is not independent of clones.
  3. condition 2': a tie of ranked pairs is removed by one more ballot, a ranking that ranked pairs
     gives for the profile; every tie of Schulze found is removed by one ballot added to ten copies.
Run: python3 equality_votes_again_rules.py   (needs numpy and scipy; under a minute)
"""
import itertools
import numpy as np

source = open(__file__.replace("equality_votes_again_rules.py", "equality_votes_again.py")).read()
exec(source[:source.index("# 1. strict rankings")])      # tree_orders, weak_orders, clone
rng = np.random.default_rng(5)


# ---------- 1. score voting ----------

def score_again(profile, m):
    """Totals as vectors over the profile and the ballots added in turn; lexicographic maximum."""
    types = {}
    for r in profile:
        types[r] = types.get(r, 0) + 1

    def go(added, left):
        totals = [tuple(sum(r[x] for r in group) for group in [profile] + [[a] for a in added]) for x in range(m)]
        top = [x for x in range(m) if totals[x] == max(totals)]
        if len(top) == 1 or not left:
            out = np.zeros(m)
            out[top] = 1 / len(top)
            return out
        total = sum(left.values())
        return sum(c / total * go(added + [t], {u: v for u, v in left.items() if u != t}) for t, c in left.items())

    return go([], types)


def score_in_turn(profile, m):
    """Section 7: each drawn voter narrows the tied candidates to those the voter scores highest."""
    types = {}
    for r in profile:
        types[r] = types.get(r, 0) + 1
    totals = [sum(r[x] for r in profile) for x in range(m)]

    def go(tied, left):
        if len(tied) == 1 or not left:
            out = np.zeros(m)
            out[tied] = 1 / len(tied)
            return out
        total = sum(left.values())
        return sum(c / total * go([x for x in tied if t[x] == max(t[y] for y in tied)],
                                  {u: v for u, v in left.items() if u != t}) for t, c in left.items())

    return go([x for x in range(m) if totals[x] == max(totals)], types)


for K in (1, 2, 5):
    ties = 0
    for _ in range(300):
        m = int(rng.integers(3, 5))
        prof = [tuple(int(v) for v in rng.integers(0, K + 1, size=m)) for _ in range(int(rng.integers(1, 6)))]
        ties += sum(score_in_turn(prof, m) > 0) > 1 or len({sum(r[x] for r in prof) for x in range(m)}) < m
        assert np.allclose(score_again(prof, m), score_in_turn(prof, m))
    print(f"1. score voting, range 0 to {K}: voting again is the tie-breaker of Section 7 on 300 random profiles")


# ---------- 2. ranked pairs and Schulze with equal ranks ----------

def vectors(profile,m,added):
    V={}
    for x in range(m):
        for y in range(m):
            if x!=y:
                V[x,y]=tuple(sum((r[y]>r[x])-(r[y]<r[x]) for r in grp) for grp in [profile]+[[a] for a in added])
    return V

def rp_winners(V,m):
    zero=tuple(0 for _ in next(iter(V.values())))
    pairs=sorted([p for p in V if V[p]>zero],key=lambda p:V[p],reverse=True)
    groups=[list(g) for _,g in itertools.groupby(pairs,key=lambda p:V[p])]
    wins=set()
    def reaches(locked,x,y):
        stack=[x];seen={x}
        while stack:
            u=stack.pop()
            if u==y:return True
            for (a,b) in locked:
                if a==u and b not in seen: seen.add(b);stack.append(b)
        return False
    def go(locked,gi):
        if gi==len(groups):
            wins.update(x for x in range(m) if not any(b==x for a,b in locked)); return
        g=groups[gi]
        seen_states=set()
        for perm in itertools.permutations(g):
            L=set(locked)
            for (a,b) in perm:
                if not reaches(L,b,a): L.add((a,b))
            f=frozenset(L)
            if f not in seen_states:
                seen_states.add(f); go(f,gi+1)
    go(frozenset(),0)
    return wins

def schulze_winners(V,m):
    zero=tuple(0 for _ in next(iter(V.values())))
    S={(x,y):(V[x,y] if V[x,y]>zero else None) for x in range(m) for y in range(m) if x!=y}
    lt=lambda a,b: (a is None and b is not None) or (a is not None and b is not None and a<b)
    mn=lambda a,b: a if lt(a,b) else b
    for k in range(m):
        for i in range(m):
            for j in range(m):
                if len({i,j,k})==3:
                    c=mn(S[i,k],S[k,j])
                    if lt(S[i,j],c): S[i,j]=c
    return {x for x in range(m) if not any(lt(S[x,y],S[y,x]) for y in range(m) if y!=x)}

stats={}
def schulze_again(profile, m, share=False):
    """Schulze with the voters voting again: ballots are drawn until one winner is left; when every
    ballot has been drawn, an order along the tree of clone sets is the last ballot, and of several
    remaining winners the one highest in it is elected (share=True: they share equally)."""
    types = {}
    for r in profile:
        types[r] = types.get(r, 0) + 1
    orders = tree_orders(list(types), m)

    def one(x):
        out = np.zeros(m)
        out[x] = 1
        return out

    def go(added, left):
        W = schulze_winners(vectors(profile, m, added), m)
        if len(W) == 1:
            return one(min(W))
        if not left:
            out = np.zeros(m)
            for order, w in orders.items():
                pos = tuple(order.index(x) for x in range(m))
                W2 = schulze_winners(vectors(profile, m, added + [pos]), m)
                stats["several"] += len(W2) > 1
                if share:
                    out[list(W2)] += w / len(W2)
                else:
                    out += w * one(min(W2, key=lambda x: pos[x]))
            return out
        total = sum(left.values())
        return sum(c / total * go(added + [t], {u: v for u, v in left.items() if u != t}) for t, c in left.items())

    return go([], types)


def ranked_pairs_again(profile, m):
    """Ranked pairs with the voters voting again: every ballot is drawn, then an order of the candidates
    along the tree of clone sets; pairs with equal lists are ordered by that order as Zavist and Tideman
    order tied pairs by a ballot (by the higher candidate of the pair, then by the lower)."""
    types = {}
    for r in profile:
        types[r] = types.get(r, 0) + 1
    orders = tree_orders(list(types), m)

    def winner(V, pos):
        zero = tuple(0 for _ in next(iter(V.values())))
        pairs = sorted([p for p in V if V[p] > zero],
                       key=lambda p: (tuple(-v for v in V[p]), min(pos[p[0]], pos[p[1]]), max(pos[p[0]], pos[p[1]])))
        locked = set()
        for a, b in pairs:
            stack, seen = [b], {b}
            while stack:
                u = stack.pop()
                for c, d in locked:
                    if c == u and d not in seen:
                        seen.add(d)
                        stack.append(d)
            if a not in seen:
                locked.add((a, b))
        return next(x for x in range(m) if not any(b == x for _, b in locked))

    def go(added, left):
        out = np.zeros(m)
        if not left:
            for order, w in orders.items():
                pos = tuple(order.index(x) for x in range(m))
                out[winner(vectors(profile, m, added + [pos]), pos)] += w
            return out
        total = sum(left.values())
        return sum(c / total * go(added + [t], {u: v for u, v in left.items() if u != t}) for t, c in left.items())

    return go([], types)


# a profile at which locking equal lists in every order leaves two winners at the last step
read = lambda text: tuple(text.index(x) for x in "abcd")
seven = [read(t) for t in ["abcd"] * 2 + ["cdab"] * 2 + ["dbca", "dbac", "bdca"]]
last = vectors(seven, 4, [read(t) for t in ["abcd", "cdab", "dbca", "dbac", "bdca"]] + [read("abcd")])
assert rp_winners(last, 4) == {1, 3}
L = ranked_pairs_again(seven, 4)
for x in range(4):
    for level in (-0.5, 0.5):
        L2 = ranked_pairs_again([canonical(list(r) + [r[x] + level]) for r in seven], 5)
        merged = L2[:4].copy()
        merged[x] += L2[4]
        assert np.allclose(merged, L)
print("2. ranked pairs, seven voters, four candidates: with equal lists locked in every order two winners are left"
      " at a last step;\n   with equal lists ordered by the last ballot the lottery is", L.round(4),
      "and is independent of clones")

for m, trials in [(3, 300), (4, 150)]:
    W = weak_orders(m)
    tested = 0
    for _ in range(trials):
        prof = [W[i] for i in rng.integers(len(W), size=int(rng.integers(1, 6)))]
        x = int(rng.integers(m))
        if any(all(r[y] == r[x] for r in prof) for y in range(m) if y != x):
            continue
        tested += 1
        L, L2 = ranked_pairs_again(prof, m), ranked_pairs_again(clone(prof, x, m), m + 1)
        merged = L2[:m].copy()
        merged[x] += L2[m]
        assert np.allclose(merged, L, atol=1e-9), (prof, x, L, L2)
    print(f"2. ranked pairs, {m} candidates: independent of clones on {tested} random profiles outside the exception")

# a profile at which sharing equally among several Schulze winners is not independent of clones:
# a cycle of x, y, z with x replaced by clones a, A that half of the voters order each way
read = lambda text, names: tuple(text.index(x) for x in names)
cycle = [read(t, "aAyz") for t in ["aAyz", "Aayz", "yzaA", "yzAa", "zaAy", "zAay"]]
split = [canonical(list(r) + [r[0] + (-0.5 if i % 2 == 0 else 0.5)]) for i, r in enumerate(cycle)]   # a cloned
stats["several"] = 0
before, after = schulze_again(cycle, 4, share=True), schulze_again(split, 5, share=True)
assert np.isclose(before[1], 1 / 6) and np.isclose(after[1], 1 / 9)
before, after = schulze_again(cycle, 4), schulze_again(split, 5)
assert np.allclose(after[1:4], before[1:4]) and np.isclose(after[0] + after[4], before[0])
print("2. Schulze, a cycle with two clones, one of them cloned again: with several winners sharing equally the"
      " other clone falls from 1/6 to 1/9;\n   with the winner highest in the last ballot the rule is independent"
      " of clones")

for m, trials in [(3, 200), (4, 60)]:
    W = weak_orders(m)
    tested = 0
    stats["several"] = 0
    for _ in range(trials):
        prof = [W[i] for i in rng.integers(len(W), size=int(rng.integers(1, 6)))]
        x = int(rng.integers(m))
        if any(all(r[y] == r[x] for r in prof) for y in range(m) if y != x):
            continue
        tested += 1
        L, L2 = schulze_again(prof, m), schulze_again(clone(prof, x, m), m + 1)
        merged = L2[:m].copy()
        merged[x] += L2[m]
        assert np.allclose(merged, L, atol=1e-9), (prof, x, L, L2)
    print(f"2. Schulze, {m} candidates: independent of clones on {tested} random profiles outside the exception;"
          f" several winners at {stats['several']} last steps")

# ---------- 3. condition 2' ----------

def a_ranking(profile, m):
    """A ranking that ranked pairs gives for the profile, with tied pairs in some order."""
    V = vectors(profile, m, [])
    pairs = sorted([p for p in V if V[p] > (0,)], key=lambda p: V[p], reverse=True)
    above = {x: {x} for x in range(m)}          # above[x]: candidates with a locked path to x, and x
    for a, b in pairs:
        if b not in above[a]:
            for x in range(m):
                if b in above[x]:
                    above[x] |= above[a]
    order = sorted(range(m), key=lambda x: len(above[x]))
    for a in range(m):                          # complete to a strict order
        for b in range(m):
            assert not (a in above[b] and a != b) or order.index(a) < order.index(b)
    return tuple(order.index(x) for x in range(m))


for m, trials in [(3, 300), (4, 100)]:
    W = weak_orders(m)
    ties = 0
    for _ in range(trials):
        prof = [W[i] for i in rng.integers(len(W), size=int(rng.integers(1, 6)))]
        if len(rp_winners(vectors(prof, m, []), m)) == 1:
            continue
        ties += 1
        assert len(rp_winners(vectors(prof + [a_ranking(prof, m)], m, []), m)) == 1, prof
    print(f"3. ranked pairs, {m} candidates: each of {ties} ties among {trials} random profiles is removed by one"
          f" more ballot, a ranking that ranked pairs gives for the profile (Proposition 19)")

for m, trials in [(3, 150), (4, 40)]:
    W = weak_orders(m)
    ties = 0
    for _ in range(trials):
        prof = [W[i] for i in rng.integers(len(W), size=int(rng.integers(1, 6)))]
        if len(schulze_winners(vectors(prof, m, []), m)) == 1:
            continue
        ties += 1
        assert any(len(schulze_winners(vectors(prof * 10 + [r], m, []), m)) == 1 for r in W), prof
    print(f"3. Schulze, {m} candidates: each of {ties} ties among {trials} random profiles is removed by one ballot"
          f" added to ten copies")
print("all checks passed")
