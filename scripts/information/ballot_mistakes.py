"""Laslier's binomial model at finite electorates, with exact best replies.

Every voter marks a ballot; each mark is recorded with probability 19/20, independently (Laslier 2006:
a mark may be lost, never added). The others' intended tallies are the poll; the realised tallies are
independent binomials, the voter's own marks are recorded with the same probability, and the winner is
drawn uniformly among the highest totals. All probabilities are integers over powers of 20, so the
comparisons of expected utility are exact however small the probabilities of ties.

1. Laslier's pivot events pivot(n, {x, y}) (x and y within one vote at the top, the others lower):
   for candidates ranked third or lower, the ratios between their ties with different candidates
   above them converge to positive constants, close to ((s_y - s_x) / (s_a1 - s_x))^2, and do not
   tend to zero (the second half of Laslier's Lemma 2). The ties of the front-runners separate
   exponentially. With symmetric errors (a mark is also added with probability 1/20) the ratios do
   tend to zero, slowly.
2. Exact best replies: plurality's best vote is the preferred front-runner once the electorate is
   moderately large; approval's best ballot differs from the leader rule for a large share of random
   voters at every size, and a threshold against a lottery over the candidates ranked above, with
   weights (s_y - s_x)^2, agrees with them more often than the leader rule but not always. With four
   or more candidates a few exact best ballots are insincere (they approve a candidate and leave out
   one the voter prefers to it).
3. A profile in which the Condorcet winner c is the lukewarm second choice of two camps: the poll
   (a1, a2) with c third reproduces itself exactly under exact best replies, for 100 to 800 voters, so
   it is an equilibrium in Laslier's sense in which the Condorcet winner loses (Laslier's Corollary 2
   fails in the model with lost marks). Under symmetric errors it is still an equilibrium at 100 and
   200 voters and not at 400.
Run: python3 ballot_mistakes.py   (pure Python; about half a minute)
"""
import itertools
import random
from fractions import Fraction
from math import comb

DEN, LOST = 20, 1                     # a mark is lost with probability 1/20
KEPT = DEN - LOST


def pmf_lost(n, N=None):
    """Bin(n, 19/20): numerators over 20^n."""
    return [comb(n, k) * KEPT**k * LOST**(n - k) for k in range(n + 1)]


def pmf_symmetric(n, N):
    """Bin(n, 19/20) + Bin(N - n, 1/20): numerators over 20^N."""
    a = pmf_lost(n)
    b = [comb(N - n, k) * KEPT**(N - n - k) for k in range(N - n + 1)]
    out = [0] * (N + 1)
    for i, x in enumerate(a):
        for j, y in enumerate(b):
            out[i + j] += x * y
    return out


def with_own(pmf, mark):
    """Add the voter's own mark, recorded with probability 19/20 (one more factor 20 in the denominator)."""
    if not mark:
        return [v * DEN for v in pmf] + [0]
    out = [0] * (len(pmf) + 1)
    for k, v in enumerate(pmf):
        out[k] += v * LOST
        out[k + 1] += v * KEPT
    return out


def cdfs(pmfs):
    top = max(len(p) for p in pmfs)
    out = []
    for p in pmfs:
        c, s = [], 0
        for i in range(top + 2):
            c.append(s)                # c[i] = numerator of P(S < i)
            s += p[i] if i < len(p) else 0
        out.append(c)
    return out, top


def win_numerators(pmfs):
    """Numerators of P(x wins) (fair lottery among the highest), scaled by 60: sum over levels i of
    p_x(i) times the integral over t of prod_k (P(S_k < i) + P(S_k = i) t)."""
    m = len(pmfs)
    cdf, top = cdfs(pmfs)
    res = []
    for x in range(m):
        tot = 0
        for i, px in enumerate(pmfs[x]):
            if px == 0:
                continue
            poly = [1]
            for k in range(m):
                if k == x:
                    continue
                a = pmfs[k][i] if i < len(pmfs[k]) else 0
                f = cdf[k][min(i, top + 1)]
                new = [0] * (len(poly) + 1)
                for j, cj in enumerate(poly):
                    new[j] += cj * f
                    new[j + 1] += cj * a
                poly = new
            tot += px * sum(cj * (60 // (j + 1)) for j, cj in enumerate(poly))
        res.append(tot)
    return res


def best_replies(counts, u, ballots, pmf=pmf_lost, N=None):
    """The best ballots of a voter with utilities u, against the others' intended tallies `counts`;
    N is the number of other voters (used by the symmetric model)."""
    base = [pmf(n, N) for n in counts]
    vals = []
    for b in ballots:
        w = win_numerators([with_own(base[k], b[k]) for k in range(len(counts))])
        vals.append(sum(ux * wx for ux, wx in zip(u, w)))
    top = max(vals)
    return [b for b, v in zip(ballots, vals) if v == top]


def pivot(pmfs, x, y):
    """Laslier's pivot(n, {x, y}), numerator over the common denominator."""
    cdf, top = cdfs(pmfs)
    tot = 0
    for sx, px in enumerate(pmfs[x]):
        for sy in (sx - 1, sx, sx + 1):
            if not 0 <= sy < len(pmfs[y]):
                continue
            M, term = max(sx, sy), px * pmfs[y][sy]
            for k in range(len(pmfs)):
                if k not in (x, y):
                    term *= cdf[k][M - 1] if M >= 1 else 0
            tot += term
    return tot


def ratio_table(pmf, sizes):
    shares = (0.55, 0.45, 0.35, 0.20)
    print("    N   {1,3}/{1,2}   {3,2}/{3,1}   {4,2}/{4,1}   {4,3}/{4,1}")
    for N in sizes:
        counts = [round(s * N) for s in shares]
        pm = [pmf(n, N) for n in counts]
        r = lambda a, b: float(Fraction(pivot(pm, *a), pivot(pm, *b)))
        print(f"{N:5d}  {r((0, 2), (0, 1)):11.3e}  {r((2, 1), (2, 0)):11.3e}  {r((3, 1), (3, 0)):11.3e}"
              f"  {r((3, 2), (3, 0)):11.3e}")
    lim = lambda y, x: ((shares[y] - shares[x]) / (shares[0] - shares[x])) ** 2
    print(f"  ((s_y - s_x)/(s_a1 - s_x))^2:     {lim(1, 2):.3f}        {lim(1, 3):.3f}        {lim(2, 3):.3f}")


def weighted_rule(u, s):
    m = len(u)
    order = sorted(range(m), key=lambda x: -s[x])
    a1, a2 = order[0], order[1]
    b = [0] * m
    b[a1], b[a2] = int(u[a1] > u[a2]), int(u[a2] > u[a1])
    for k in range(2, m):
        x, above = order[k], order[:k]
        w = [(s[y] - s[x]) ** 2 for y in above]
        b[x] = int(u[x] > sum(wi * u[y] for wi, y in zip(w, above)) / sum(w))
    return tuple(b)


def main():
    random.seed(1)
    print("1. Ratios of pivot probabilities, shares (0.55, 0.45, 0.35, 0.20); marks lost only:")
    ratio_table(pmf_lost, (20, 80, 320, 1280))
    print("   marks lost and added (symmetric):")
    ratio_table(pmf_symmetric, (20, 80, 320))

    print("2. Exact best replies for random utilities, four candidates:")
    m = 4
    appr = list(itertools.product((0, 1), repeat=m))
    plur = [tuple(int(k == c) for k in range(m)) for c in range(m)]
    shares_a, shares_p = (0.55, 0.45, 0.35, 0.20), (0.36, 0.33, 0.30, 0.01)
    for N in (40, 160, 640):
        ca, cp = [round(s * N) for s in shares_a], [round(s * N) for s in shares_p]
        T, lr_ok, w_ok, p_ok = 40, 0, 0, 0
        for t in range(T):
            u = random.sample(range(1, 1000), m)
            a = best_replies(ca, u, appr)
            lr = [int(u[x] > u[0]) for x in range(m)]
            lr[0] = int(u[0] > u[1])
            lr_ok += a == [tuple(lr)]
            w_ok += a == [weighted_rule(u, shares_a)]
            p = best_replies(cp, u, plur)
            p_ok += p == [tuple(int(k == (0 if u[0] > u[1] else 1)) for k in range(m))]
        print(f"   N = {N:4d}: approval = leader rule {lr_ok}/{T}, = weighted rule {w_ok}/{T}; "
              f"plurality (close race of three) = preferred front-runner {p_ok}/{T}")
    shares5 = (0.55, 0.45, 0.35, 0.25, 0.12)
    ballots5 = list(itertools.product((0, 1), repeat=5))
    u = [410, 601, 43, 404, 24]
    b = best_replies([round(s * 320) for s in shares5], u, ballots5)
    print(f"   five candidates, 320 voters, utilities {u}: best ballot {b[0]}, insincere: "
          f"{b == [(0, 1, 0, 1, 0)]}")

    print("3. The Condorcet winner as lukewarm second choice (candidates a1, a2, c):")
    types = [(10, (500, 0, 1000)), (42, (0, 1000, 250)), (42, (1000, 0, 400)),
             (4, (1000, 500, 0)), (2, (500, 1000, 0))]
    pref = lambda x, y: sum(w for w, u in types if u[x] > u[y])
    print(f"   per 100 voters: c beats a1 {pref(2, 0)}-{pref(0, 2)} and a2 {pref(2, 1)}-{pref(1, 2)}; "
          f"a1 beats a2 {pref(0, 1)}-{pref(1, 0)}")
    ballots = list(itertools.product((0, 1), repeat=3))
    for label, pmf, sizes in (("marks lost only", pmf_lost, (1, 2, 4, 8)),
                              ("symmetric errors", pmf_symmetric, (1, 2, 4))):
        for R in sizes:
            poll = [56 * R, 44 * R, 10 * R]
            tally = [0, 0, 0]
            for w, u in types:
                b = best_replies(poll, list(u), ballots, pmf, 100 * R)
                assert len(b) == 1
                tally = [t + w * R * bk for t, bk in zip(tally, b[0])]
            print(f"   {label}, N = {100 * R}: poll {poll}, tally of exact best replies {tally}, "
                  f"self-confirming: {tally == poll}")


if __name__ == "__main__":
    main()
