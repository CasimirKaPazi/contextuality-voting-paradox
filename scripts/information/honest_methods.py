"""The honest measure for three candidates (*The Honest Axis*, Section 5).

Every voter casts the honest ballot of *The Honest Axis*, Section 1: the favourite (plurality), the
candidates above the voter's mean utility (approval), the range-normalised utilities rounded to
scores 0..k (score, k = 2, 5, and a continuous scale), the ranking (Borda, instant runoff,
BTR-plurality), the utilities with mean zero and variance one (round ballots).  Profiles as in
smooth_methods.py: 101 voters, impartial culture with random utilities and a two-dimensional spatial
model; first the 40 profiles per model used there, then 4000 fresh ones.

For each method: how often the honest winner is the Condorcet winner (among profiles with one), the
candidate with the largest total utility, and the candidate with the largest total of
range-normalised utilities; and the mean total utility of the winner on the scale where the average
candidate is 0 and the best is 1.  A few seconds.
"""
import numpy as np
from irv_smooth import condorcet_winner, profile


def pairwise(U, x, y):
    return (U[:, x] > U[:, y]).sum() > len(U) / 2


def winners(U):
    n = len(U)
    lo, hi = U.min(1, keepdims=True), U.max(1, keepdims=True)
    nu = (U - lo) / (hi - lo)
    first = np.bincount(np.argmax(U, 1), minlength=3)
    order = np.argsort(first, kind='stable')
    b, mid, top = order
    out = {'plurality': int(np.argmax(first)),
           'approval': int(np.argmax((U > U.mean(1, keepdims=True)).sum(0))),
           'score 0..2': int(np.argmax(np.rint(2 * nu).sum(0))),
           'score 0..5': int(np.argmax(np.rint(5 * nu).sum(0))),
           'score, continuous': int(np.argmax(nu.sum(0))),
           'Borda': int(np.argmax(np.argsort(np.argsort(U, 1), 1).sum(0))),
           'round ballots': int(np.argmax(((U - U.mean(1, keepdims=True)) / U.std(1, keepdims=True)).sum(0)))}
    x, y = (c for c in range(3) if c != b)
    out['instant runoff'] = int(x if pairwise(U, x, y) else y)
    s = b if pairwise(U, b, mid) else mid
    out['BTR-plurality'] = int(s if pairwise(U, s, top) else top)
    return out, int(np.argmax(nu.sum(0)))


def measure(model, profiles, seed):
    rng = np.random.default_rng(seed)
    stat = {}
    cws = 0
    for _ in range(profiles):
        U = profile(model, 101, rng)
        c = condorcet_winner(U)
        cws += c is not None
        tot = U.sum(0)
        best = int(np.argmax(tot))
        won, best_nu = winners(U)
        for m, w in won.items():
            S = stat.setdefault(m, [0, 0, 0, 0.0])
            S[0] += c is not None and w == c
            S[1] += w == best
            S[2] += w == best_nu
            S[3] += (tot[w] - tot.mean()) / (tot.max() - tot.mean())
    print(f"{model}, {profiles} profiles ({cws} with a Condorcet winner)")
    for m, S in stat.items():
        print(f"   {m:18s} Condorcet winner {100 * S[0] / cws:5.1f}%, utilitarian winner {100 * S[1] / profiles:5.1f}%, "
              f"range-normalised utilitarian winner {100 * S[2] / profiles:5.1f}%, mean utility {S[3] / profiles:.3f}")


if __name__ == "__main__":
    for model in ('ic', 'spatial'):
        measure(model, 40, 11)
        measure(model, 4000, 12)
