"""Five methods with three candidates in one smooth model (*The Smooth Model across Methods*).

Plurality, approval, Borda, instant runoff and BTR-plurality on the same profiles (101 voters, 40 per
model; impartial culture with random utilities, and a two-dimensional spatial model), with the model
of irv_smooth.py: a poll is a vector of expected shares of the method's ballots; every voter believes
the other ballots to have shares drawn from a Dirichlet distribution around the poll with precision s
(plus one half per ballot) and casts the ballot with the highest expected utility when added with
weight 0.002 (6000 samples, the same for every ballot); ties go to the most sincere ballot.  The poll
moves 5 per cent towards the shares of the best replies, for 300 rounds.  A run comes to rest if the
winner of the poll is the same over the last 100 rounds and no share moved by more than 0.03 over
them.  Starting polls: a sincere one, polls concentrated on a pair of front-runners, three random
ones (ten per method, seven for plurality).  Random numbers are drawn as in irv_smooth.py,
btr_smooth.py and additive_smooth.py, whose counts this script reproduces.

For each method: runs at rest; under the majority target, the profiles with a Condorcet winner at
which some resting poll elects another candidate and those without a resting poll; under the
utilitarian target, the profiles at which some resting poll elects a candidate other than the one
with the largest total utility; and over the runs at rest, how often the Condorcet winner and the
utilitarian winner are elected, and the mean utility of the winner on the scale where the average
candidate is 0 and the best is 1.
Run: python3 smooth_methods.py MODEL PRECISION (for instance ic 85); about forty minutes per call.
"""
import itertools
import sys
import numpy as np
from irv_smooth import RANK, FIRST, ABOVE, inversions, condorcet_winner, profile
from irv_smooth import sincere as rank_sincere, starts as rank_starts
from additive_smooth import VEC, sincere as add_sincere, starts as add_starts

FP = np.array([[float(r[0] == c) for r in RANK] for c in range(3)])      # 3 x 6
METHODS = ('plurality', 'approval', 'borda', 'irv', 'btr')
NB = {'plurality': 3, 'approval': 8, 'borda': 6, 'irv': 6, 'btr': 6}


def winners(method, S, delta):
    """For every ballot b, the winners of the K samples S with b added at weight delta."""
    K = len(S)
    i = np.arange(K)
    out = []
    if method == 'plurality':
        for b in range(3):
            T = S.copy()
            T[:, b] += delta
            out.append(np.argmax(T, 1))
        return out
    if method in VEC:
        V = VEC[method]
        tot = S @ V
        return [np.argmax(tot + delta * V[b], 1) for b in range(len(V))]
    F0 = S @ FP.T
    P0 = np.einsum('kb,xyb->kxy', S, ABOVE)
    for b in range(6):
        F = F0 + delta * FP[:, b]
        P = P0 + delta * ABOVE[:, :, b]
        o = np.argsort(F, 1)
        lo, mid, top = o[:, 0], o[:, 1], o[:, 2]
        if method == 'irv':
            out.append(np.where(P[i, mid, top] > P[i, top, mid], mid, top))
        else:
            s = np.where(P[i, lo, mid] > P[i, mid, lo], lo, mid)
            out.append(np.where(P[i, s, top] > P[i, top, s], s, top))
    return out


def poll_winner(method, v):
    return int(winners(method, v[None], 0.0)[0][0])


def best_replies(U, v, method, s, rng, delta=0.002, K=6000):
    S = rng.dirichlet(s * v + 0.5, size=K)
    P = np.array([np.bincount(w, minlength=3) / K for w in winners(method, S, delta)])
    EU = U @ P.T
    best = []
    for j, u in enumerate(U):
        cand = np.where(EU[j] >= EU[j].max() - 1e-12)[0]
        if method == 'plurality':
            best.append(max(cand, key=lambda b: u[b]))
        elif method == 'approval':
            best.append(max(cand, key=lambda b: VEC['approval'][b] @ (u - u.mean())))
        else:
            best.append(min(cand, key=lambda b: inversions(u, b)))
    return np.array(best)


def run(U, method, v, s, rng, lam=0.05, T=300):
    vs, ws = [], []
    for _ in range(T):
        b = best_replies(U, v, method, s, rng)
        v = (1 - lam) * v + lam * np.bincount(b, minlength=NB[method]) / len(U)
        vs.append(v.copy())
        ws.append(poll_winner(method, v))
    rest = len(set(ws[-100:])) == 1 and np.abs(vs[-1] - vs[-101]).max() < 0.03
    return rest, ws[-1], v


def all_starts(U, p):
    r = np.random.default_rng(100 + p)
    out = {'irv': rank_starts(U, 'irv', r)}
    out['plurality'] = rank_starts(U, 'plurality', r)
    out['btr'] = rank_starts(U, 'irv', np.random.default_rng(100 + p))
    r = np.random.default_rng(100 + p)
    out['approval'] = add_starts(U, 'approval', r)
    out['borda'] = add_starts(U, 'borda', r)
    return out


def main(model, s, profiles=40):
    rng = np.random.default_rng(11)
    keys = ('runs', 'rest', 'cw', 'other', 'none', 'no_cw', 'no_cw_rest', 'util_other', 'cw_runs', 'cw_won',
            'util_won')
    stat = {m: dict.fromkeys(keys, 0) for m in METHODS}
    gain = {m: 0.0 for m in METHODS}
    for p in range(profiles):
        U = profile(model, 101, rng)
        c = condorcet_winner(U)
        tot = U.sum(0)
        best = int(np.argmax(tot))
        st = all_starts(U, p)
        for m in METHODS:
            S, won = stat[m], set()
            for k, v0 in enumerate(st[m]):
                rest, w, v = run(U, m, v0.copy(), s, np.random.default_rng(1000 * p + k))
                S['runs'] += 1
                if not rest:
                    continue
                S['rest'] += 1
                won.add(w)
                S['util_won'] += w == best
                gain[m] += (tot[w] - tot.mean()) / (tot.max() - tot.mean())
                if c is not None:
                    S['cw_runs'] += 1
                    S['cw_won'] += w == c
            S['util_other'] += any(w != best for w in won)
            if c is None:
                S['no_cw'] += 1
                S['no_cw_rest'] += bool(won)
            else:
                S['cw'] += 1
                S['none'] += not won
                S['other'] += any(w != c for w in won)
        print(f"# profile {p} done", file=sys.stderr, flush=True)
    for m in METHODS:
        S = stat[m]
        print(f"{model:8s} s = {s:g}  {m:9s} runs at rest {S['rest']}/{S['runs']}; majority target, "
              f"{S['cw']} profiles with a Condorcet winner: another winner at some resting poll {S['other']}, "
              f"no resting poll {S['none']}; without one ({S['no_cw']}): some resting poll {S['no_cw_rest']}; "
              f"utilitarian target, {profiles} profiles: another winner at some resting poll "
              f"{S['util_other']}; runs at rest electing the Condorcet winner {S['cw_won']}/{S['cw_runs']}, "
              f"the utilitarian winner {S['util_won']}/{S['rest']}, mean utility {gain[m] / max(S['rest'], 1):.3f}",
              flush=True)


if __name__ == "__main__":
    main(sys.argv[1], float(sys.argv[2]))
