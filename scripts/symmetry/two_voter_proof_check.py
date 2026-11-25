"""Checks every step of the hand proof of Proposition 14 (two-voter local
unanimous rules are dictatorships) on all pairs of rankings, for m = 5, 6, 7
(note *Equivariant Obstructions*, Section 6.5a).

The proof considers a pair (s, t) at minimal distance d with F(s, t) != s.
By the steps done by hand in the note, s has exactly one adjacent pair
(alpha, beta), at positions k and k+1, ordered against t, the tops and the
bottoms of s and t differ, and F(s, t) = s1, s with alpha and beta swapped.
The script checks, for every such pair:

  shape:   t is a shuffle of u = s[:k] and v = s[k:] with beta on top and
           alpha at the bottom, and d >= m - 1, with equality exactly for
           t = beta + (u without alpha) + (v without beta) + alpha;
  d >= m:  w = t with beta moved to the bottom has d(w, t) = m - 1 < d and
           d(s1, w) = d(s, w) + 1;
  d = m-1: the chains of the note exist: the anchors share the bottom or top
           with the named neighbour of t, the forced values are the unique
           common neighbours, the end point has distance d - 1 to t, and the
           final distances (3, or 2) exceed what locality allows.

It also checks the facts about the permutohedron used: two rankings at
distance 2 that differ by two adjacent (non-commuting) swaps have exactly one
common neighbour.

Run: python3 two_voter_proof_check.py   (about twenty seconds)
"""

import itertools


def kendall(a, b):
    pb = {c: i for i, c in enumerate(b)}
    q = [pb[c] for c in a]
    return sum(1 for i in range(len(q)) for j in range(i + 1, len(q)) if q[i] > q[j])


def swap(r, i):  # i = 1-based position of the upper element
    r = list(r)
    r[i - 1], r[i] = r[i], r[i - 1]
    return tuple(r)


def neighbours(r):
    return {swap(r, i) for i in range(1, len(r))}


def ball(r):
    return neighbours(r) | {r}


def common(a, b):
    return ball(a) & ball(b)


def check_chain_A(s, t, k, m, d, s1):
    """k >= 2 and |v| >= 2: gamma = s[k-2] above alpha."""
    x1 = swap(s, k - 1)                         # gamma <-> alpha
    t_ = swap(t, m - 1)                         # alpha up one in t
    assert t_[-1] == x1[-1], "x1 shares the bottom with t'"
    assert common(x1, s1) == {s}, "G(x1) = s"
    x2 = swap(x1, k)                            # gamma <-> beta
    x3 = swap(x2, k - 1)                        # alpha <-> beta: triple reversed
    assert kendall(x3, t) == d - 1, "G(x3) = x3 by minimality"
    assert kendall(s, x3) == 3, "ball(s) and ball(x3) are disjoint"


def check_chain_B(s, t, m, d, s1):
    """k = 1: alpha on top of s, delta = s[2]."""
    x1 = swap(s, 2)                             # beta <-> delta
    t_ = swap(t, m - 1)
    assert t_[-1] == x1[-1], "x1 shares the bottom with t'"
    assert common(x1, s1) == {s}, "G(x1) = s"
    x2 = swap(x1, 1)                            # alpha <-> delta
    t__ = swap(t, 1)
    assert t__[0] == x2[0], "x2 shares the top with t''"
    assert common(x2, s) == {x1}, "G(x2) = x1"
    x3 = swap(x2, 2)                            # alpha <-> beta
    assert kendall(x3, t) == d - 1, "G(x3) = x3 by minimality"
    assert kendall(x1, x3) == 2, "locality fails between x2 and x3"


def main():
    for m in (5, 6, 7):
        P = list(itertools.permutations(range(m)))
        counts = {"d>=m": 0, "A": 0, "B": 0, "C": 0}
        for s in P:
            ps = {c: i for i, c in enumerate(s)}
            for t in P:
                if s[0] == t[0] or s[-1] == t[-1]:
                    continue
                pt = {c: i for i, c in enumerate(t)}
                steps = [i for i in range(1, m) if pt[s[i - 1]] > pt[s[i]]]
                if len(steps) != 1:
                    continue
                k = steps[0]
                alpha, beta = s[k - 1], s[k]
                u, v = s[:k], s[k:]
                s1 = swap(s, k)
                d = kendall(s, t)
                # shape
                assert [c for c in t if c in u] == list(u)
                assert [c for c in t if c in v] == list(v)
                assert t[0] == beta and t[-1] == alpha
                assert d >= m - 1
                canonical = (beta,) + u[:-1] + v[1:] + (alpha,)
                assert (d == m - 1) == (t == canonical)
                if d >= m:
                    w = tuple(c for c in t if c != beta) + (beta,)
                    assert kendall(w, t) == m - 1 < d
                    assert kendall(s1, w) == kendall(s, w) + 1
                    counts["d>=m"] += 1
                elif k >= 2 and len(v) >= 2:
                    check_chain_A(s, t, k, m, d, s1)
                    counts["A"] += 1
                elif k == 1:
                    check_chain_B(s, t, m, d, s1)
                    counts["B"] += 1
                else:  # |v| = 1: the reversed pair is of case B
                    R = lambda r: tuple(reversed(r))
                    rs, rt = R(s), R(t)
                    prs = {c: i for i, c in enumerate(rt)}
                    rsteps = [i for i in range(1, m) if prs[rs[i - 1]] > prs[rs[i]]]
                    assert rsteps == [1]
                    check_chain_B(rs, rt, m, d, swap(rs, 1))
                    counts["C"] += 1
        print(f"m = {m}: pairs with one step and differing tops and bottoms:"
              f" {sum(counts.values())}; d >= m: {counts['d>=m']};"
              f" d = m - 1, chain A: {counts['A']}, chain B: {counts['B']},"
              f" by reversal: {counts['C']}; all steps hold")


if __name__ == "__main__":
    main()
