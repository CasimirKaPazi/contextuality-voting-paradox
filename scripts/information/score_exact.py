"""Score voting with scores 0..k in Laslier's binomial model (*Score and Approval*, Section 1).

The other voters give each candidate 0 or k points, the voter any score from 0 to k; each mark is
uncounted with probability 1/20, and the winner is drawn among the highest totals. Exact best ballots,
by brute force over all score ballots, for random utilities: how often the unique best ballot uses an
intermediate score, for three and four candidates, k = 2 and 3, 10 to 80 voters. Reported, no claim.
Run: python3 score_exact.py   (pure Python; about twenty seconds)
"""
import itertools
import random
from ballot_mistakes import pmf_lost, win_numerators, LOST, KEPT, DEN


def scaled(pmf, k):
    """The others' points: k per counted mark."""
    out = [0] * (k * (len(pmf) - 1) + 1)
    for i, v in enumerate(pmf): out[k * i] = v
    return out


def with_own_s(pmf, s):
    """Add the voter's own s points, counted with probability 19/20."""
    if s == 0: return [v * DEN for v in pmf] + [0]
    out = [0] * (len(pmf) + s)
    for i, v in enumerate(pmf):
        out[i] += v * LOST; out[i + s] += v * KEPT
    return out


def best(counts, u, k):
    m = len(u); base = [scaled(pmf_lost(n), k) for n in counts]
    vals = []
    for b in itertools.product(range(k + 1), repeat=m):
        w = win_numerators([with_own_s(base[x], b[x]) for x in range(m)])
        vals.append((sum(ux * wx for ux, wx in zip(u, w)), b))
    top = max(v for v, b in vals)
    return [b for v, b in vals if v == top]


def main():
    random.seed(2)
    for m, shares in ((3, (0.55, 0.45, 0.35)), (4, (0.55, 0.45, 0.35, 0.20))):
        for k in (2, 3):
            for N in (10, 20, 40, 80):
                counts = [round(s * N) for s in shares]
                inter = uniq_inter = 0; T = 50
                for t in range(T):
                    u = random.sample(range(1, 1000), m)
                    arg = best(counts, u, k)
                    inter += any(0 < x < k for x in arg[0])
                    uniq_inter += len(arg) == 1 and any(0 < x < k for x in arg[0])
                print(f"m={m} k={k} N={N:3d}: best ballot uses an intermediate score for {uniq_inter}/{T} voters (unique best)")


if __name__ == "__main__":
    main()
