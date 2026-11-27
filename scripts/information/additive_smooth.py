"""Approval and Borda with three candidates in the smooth model of irv_smooth.py
(*The Smooth Model across Methods*, Sections 2 and 3).

The same profiles (101 voters, 40 per model, the generator and seed of irv_smooth.py), beliefs
(Dirichlet around the poll with precision s, plus one half per ballot), ballot weight 0.002, poll
dynamics (5 per cent towards the best replies, 300 rounds) and test for coming to rest as in
irv_smooth.py, so that the counts can be set beside those for plurality, instant runoff and
BTR-plurality.  A poll is a vector of expected shares of the method's ballots: the eight approval
ballots, the six Borda rankings.  Ten starting polls: a sincere one (approval of the candidates above
the voter's mean utility; the sincere ranking), six concentrated on a pair of front-runners, three
random.  Ties between best ballots go to the most sincere one.

For each profile: whether some run that comes to rest elects a candidate other than the Condorcet
winner, whether no run comes to rest; at the resting polls, the shares of the kinds of ballots.
Run: python3 additive_smooth.py MODEL PRECISION (for instance ic 85); about twenty minutes per call.
"""
import itertools
import sys
import numpy as np
from irv_smooth import RANK, FIRST, condorcet_winner, profile, starts as rank_starts, inversions

APPROVAL = [np.array(b) for b in itertools.product((0, 1), repeat=3)]
BORDA = [np.array([2 - r.index(c) for c in range(3)]) for r in RANK]
VEC = {'approval': np.array(APPROVAL, float), 'borda': np.array(BORDA, float)}


def best_replies(U, v, method, s, delta, rng, K):
    V = VEC[method]
    S = rng.dirichlet(s * v + 0.5, size=K)
    tot = S @ V
    P = np.zeros((len(V), 3))
    for b in range(len(V)):
        P[b] = np.bincount(np.argmax(tot + delta * V[b], 1), minlength=3) / K
    EU = U @ P.T
    best = []
    for i, u in enumerate(U):
        cand = np.where(EU[i] >= EU[i].max() - 1e-12)[0]
        if method == 'approval':
            best.append(max(cand, key=lambda b: V[b] @ (u - u.mean())))
        else:
            best.append(min(cand, key=lambda b: inversions(u, b)))
    return np.array(best)


def sincere(U, method):
    if method == 'borda':
        idx = [RANK.index(tuple(np.argsort(-u))) for u in U]
    else:
        idx = [int(''.join(str(int(x > u.mean())) for x in u), 2) for u in U]
    return np.bincount(idx, minlength=len(VEC[method])) / len(U)


def starts(U, method, rng):
    if method == 'borda':
        return [sincere(U, 'borda')] + rank_starts(U, 'irv', rng)[1:]
    out = [sincere(U, 'approval')]
    single = {c: int(''.join('1' if x == c else '0' for x in range(3)), 2) for c in range(3)}
    for L, R in itertools.permutations(range(3), 2):
        v = np.full(8, 0.01)
        v[single[L]] += 0.5
        v[single[R]] += 0.42
        out.append(v / v.sum())
    out += [rng.dirichlet(np.ones(8)) for _ in range(3)]
    return out


def run(U, method, v, s, rng, delta=0.002, lam=0.05, T=300, K=6000):
    V = VEC[method]
    vs, ws = [], []
    for _ in range(T):
        b = best_replies(U, v, method, s, delta, rng, K)
        v = (1 - lam) * v + lam * np.bincount(b, minlength=len(V)) / len(U)
        vs.append(v.copy())
        ws.append(int(np.argmax(v @ V)))
    rest = len(set(ws[-100:])) == 1 and np.abs(vs[-1] - vs[-101]).max() < 0.03
    return rest, ws[-1], v


def main(model, s, profiles=40):
    rng = np.random.default_rng(11)
    stat = {m: dict(cw=0, other=0, none=0, no_cw=0, no_cw_rest=0, runs=0, rest=0, cw_runs=0, cw_won=0)
            for m in VEC}
    kinds = {'approval': np.zeros(4), 'borda': np.zeros(2)}
    for p in range(profiles):
        U = profile(model, 101, rng)
        c = condorcet_winner(U)
        r = np.random.default_rng(100 + p)
        for method in VEC:
            won = set()
            S = stat[method]
            for k, v0 in enumerate(starts(U, method, r)):
                rk = np.random.default_rng(1000 * p + k)
                rest, w, v = run(U, method, v0.copy(), s, rk)
                S['runs'] += 1
                S['rest'] += rest
                if not rest:
                    continue
                won.add(w)
                if c is not None:
                    S['cw_runs'] += 1
                    S['cw_won'] += w == c
                b = best_replies(U, v, method, s, 0.002, rk, 6000)
                if method == 'approval':
                    for i in b:
                        kinds['approval'][int(VEC['approval'][i].sum())] += 1
                else:
                    for i, u in zip(b, U):
                        kinds['borda'][int(inversions(u, i) > 0)] += 1
            if c is None:
                S['no_cw'] += 1
                S['no_cw_rest'] += bool(won)
            else:
                S['cw'] += 1
                S['none'] += not won
                S['other'] += any(w != c for w in won)
    for method, S in stat.items():
        print(f"{model:8s} s = {s:g}  {method:8s} runs at rest {S['rest']}/{S['runs']}; with a Condorcet "
              f"winner ({S['cw']} profiles): some run at rest elects another candidate {S['other']}, no run "
              f"comes to rest {S['none']}, runs at rest electing the Condorcet winner "
              f"{S['cw_won']}/{S['cw_runs']}; without one ({S['no_cw']}): some run comes to rest "
              f"{S['no_cw_rest']}")
    a = kinds['approval'] / max(kinds['approval'].sum(), 1)
    b = kinds['borda'] / max(kinds['borda'].sum(), 1)
    print(f"{model:8s} s = {s:g}  approval ballots at resting polls approving 0, 1, 2, 3 candidates: "
          f"{a.round(3).tolist()}; Borda ballots at resting polls that are not the sincere ranking: {b[1]:.3f}")


if __name__ == "__main__":
    main(sys.argv[1], float(sys.argv[2]))
