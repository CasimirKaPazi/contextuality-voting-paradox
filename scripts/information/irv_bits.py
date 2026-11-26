"""Stage 2 in bits for instant runoff and plurality with three candidates in the smooth model of
`irv_smooth.py` (*Instant Runoff and Plurality*, Section 7; *Strategic Information*, README, Section 2).

At a fixed poll a strategic ballot is a function of the voter's utilities.  For a distribution of
voters (the culture of the profile: impartial culture with random utilities, or the spatial model
with the profile's candidates) the script estimates, from 4000 fresh voters:

  H(IRV), H(plur)   the entropy of the strategic ballot in bits (stage 2 per voter; the capacities
                    of stage 1 are log2 6 = 2.58 and log2 3 = 1.58 bits);
  H(plur | IRV)     what the plurality ballot says that the IRV ballot does not; zero exactly when
                    the plurality ballot is a function of the IRV ballot, which by the lemma of the
                    README, Section 2, is Blackwell's order at that poll;
  H(IRV | plur)     the converse;
  H(plur | ranking), H(plur | IRV, ranking)   how much of the plurality ballot depends on intensities.

Two ways of matching the polls of the two methods are used: (a) each method at its own settled poll,
reached from the sincere ballots as in `irv_smooth.py`; (b) the plurality poll given by the first
preferences of the settled IRV poll (the matching induced by the embedding of stage 1).
Profiles of 101 voters, 20 per model, precisions 85 and 20.  A few minutes per model and precision.
"""
import sys
from collections import Counter
from math import log2
import numpy as np
from irv_smooth import FIRST, run, sincere, best_replies


def H(xs):
    c, n = Counter(xs), len(xs)
    return -sum(v / n * log2(v / n) for v in c.values())


def Hc(a, b):
    return H(list(zip(a, b))) - H(list(b))


def voters(model, rng, n, cand):
    if model == 'ic':
        return rng.random((n, 3))
    V = rng.normal(size=(n, 2))
    return -np.linalg.norm(V[:, None, :] - cand[None], axis=2)


def main(model, s, profiles=20):
    rng = np.random.default_rng(5)
    own, proj = [], []
    for p in range(profiles):
        cand = rng.normal(size=(3, 2))
        U = voters(model, rng, 101, cand)
        X = voters(model, rng, 4000, cand)
        rk = np.random.default_rng(p)
        si, wi, v = run(U, 'irv', sincere(U, 'irv'), s, rk)
        sp, wp, w = run(U, 'plurality', sincere(U, 'plurality'), s, rk)
        if not si:
            continue
        rank = [tuple(np.argsort(-u)) for u in X]
        bi = list(best_replies(X, v, 'irv', s, 0.002, rk, 20000))
        vp = np.array([v[FIRST == c].sum() for c in range(3)])
        bq = list(best_replies(X, vp, 'plurality', s, 0.002, rk, 20000))
        proj.append((H(bi), H(bq), Hc(bq, bi), Hc(bi, bq), Hc(bq, rank), Hc(bq, list(zip(bi, rank)))))
        if sp:
            bp = list(best_replies(X, w, 'plurality', s, 0.002, rk, 20000))
            own.append((H(bi), H(bp), Hc(bp, bi), Hc(bi, bp), wi == wp))
    for name, R in (('own settled polls', np.array(own, float)), ('first preferences', np.array(proj, float))):
        line = (f"{model:8s} s = {s:g}  {name:17s} ({len(R)} polls): H(IRV) {R[:, 0].mean():.2f}, "
                f"H(plur) {R[:, 1].mean():.2f}, H(plur | IRV) {R[:, 2].mean():.3f} (max {R[:, 2].max():.3f}, "
                f"zero at {(R[:, 2] < 1e-9).sum()}), H(IRV | plur) {R[:, 3].mean():.2f}")
        if name == 'own settled polls':
            line += f"; same winner at {int(R[:, 4].sum())}"
        else:
            line += f"; H(plur | ranking) {R[:, 4].mean():.3f}, H(plur | IRV, ranking) {R[:, 5].mean():.3f}"
        print(line)


if __name__ == "__main__":
    if len(sys.argv) > 2:
        main(sys.argv[1], float(sys.argv[2]))
    else:
        for model in ('spatial', 'ic'):
            for s in (85, 20):
                main(model, s)
