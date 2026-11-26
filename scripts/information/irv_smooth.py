"""Instant runoff and plurality with three candidates when voters weigh all pivot events through a
common belief about the other ballots (*Instant Runoff and Plurality*, Section 6).

The poll is a vector v of expected ballot shares (six rankings for instant runoff, three names for
plurality).  Every voter believes that the other ballots have shares drawn from a Dirichlet
distribution with mean close to v and precision s (as in Eggers and Nowacki), and values a ballot
by the expected utility of the winner when the ballot is added with weight delta = 0.002 (about 500
voters).  Expectations are estimated with K samples, the same samples for every ballot, so that only
the samples in which a ballot is pivotal make a difference.  Remaining ties between ballots are
broken towards the sincere ballot.  Polls move as in Eggers and Nowacki: v <- (1 - lam) v + lam BR(v),
lam = 0.05, for 300 rounds, from ten starting polls (sincere ballots, polls concentrated on each pair
of front-runners, three random polls).  A run counts as settled if the winner of the poll is the same
over the last 100 rounds and no share moved by more than 0.03 over them.

For each profile (101 voters, impartial culture with random utilities and a two-dimensional spatial
model) the script records whether some settled run ends with a winner other than the Condorcet
winner, whether no run settles, and, at the settled IRV polls, how many best replies rank the two
finalists against the voter's preference.  About a quarter of an hour per model and precision.
"""
import itertools
import sys
import numpy as np

RANK = list(itertools.permutations(range(3)))
FIRST = np.array([r[0] for r in RANK])
ABOVE = np.zeros((3, 3, 6))
for b, r in enumerate(RANK):
    for i in range(3):
        for j in range(i + 1, 3):
            ABOVE[r[i], r[j], b] = 1


def irv_winner(S):
    f = np.stack([S[:, FIRST == c].sum(1) for c in range(3)], 1)
    lo = np.argmin(f, 1)
    W = np.empty(len(S), int)
    for e in range(3):
        m = lo == e
        x, y = [c for c in range(3) if c != e]
        W[m] = np.where(S[m] @ ABOVE[x, y] > S[m] @ ABOVE[y, x], x, y)
    return W


def plurality_winner(S):
    return np.argmax(S, 1)


def inversions(u, b):
    r = RANK[b]
    return sum(1 for i in range(3) for j in range(i + 1, 3) if u[r[i]] < u[r[j]])


def best_replies(U, v, method, s, delta, rng, K):
    nb = len(v)
    S = rng.dirichlet(s * v + 0.5, size=K)
    win = irv_winner if method == 'irv' else plurality_winner
    P = np.zeros((nb, 3))
    for b in range(nb):
        T = S.copy()
        T[:, b] += delta
        P[b] = np.bincount(win(T), minlength=3) / K
    EU = U @ P.T
    best = []
    for i, u in enumerate(U):
        cand = np.where(EU[i] >= EU[i].max() - 1e-12)[0]
        if method == 'irv':
            best.append(min(cand, key=lambda b: inversions(u, b)))
        else:
            best.append(max(cand, key=lambda b: u[b]))
    return np.array(best)


def sincere(U, method):
    if method == 'irv':
        return np.bincount([RANK.index(tuple(np.argsort(-u))) for u in U], minlength=6) / len(U)
    return np.bincount(np.argmax(U, 1), minlength=3) / len(U)


def starts(U, method, rng):
    out = [sincere(U, method)]
    for L, R in itertools.permutations(range(3), 2):
        if method == 'irv':
            v = np.full(6, 0.02)
            v[FIRST == L] += 0.27
            v[FIRST == R] += 0.2
            out.append(v / v.sum())
        elif L < R:
            v = np.full(3, 0.04)
            v[L] += 0.5
            v[R] += 0.44
            out.append(v / v.sum())
    out += [rng.dirichlet(np.ones(6 if method == 'irv' else 3)) for _ in range(3)]
    return out


def run(U, method, v, s, rng, delta=0.002, lam=0.05, T=300, K=6000):
    win = irv_winner if method == 'irv' else plurality_winner
    vs, ws = [], []
    for _ in range(T):
        b = best_replies(U, v, method, s, delta, rng, K)
        v = (1 - lam) * v + lam * np.bincount(b, minlength=len(v)) / len(U)
        vs.append(v.copy())
        ws.append(int(win(v[None])[0]))
    settled = len(set(ws[-100:])) == 1 and np.abs(vs[-1] - vs[-101]).max() < 0.03
    return settled, ws[-1], v


def condorcet_winner(U):
    for x in range(3):
        if all((U[:, x] > U[:, y]).sum() > len(U) / 2 for y in range(3) if y != x):
            return x


def profile(model, n, rng):
    if model == 'ic':
        return rng.random((n, 3))
    cand, V = rng.normal(size=(3, 2)), rng.normal(size=(n, 2))
    return -np.linalg.norm(V[:, None, :] - cand[None], axis=2)


def main(model, s, profiles=40):
    rng = np.random.default_rng(11)
    stat = {m: dict(cw=0, other=0, none=0, no_cw=0, no_cw_settled=0) for m in ('irv', 'plurality')}
    misordered = [0, 0]
    for p in range(profiles):
        U = profile(model, 101, rng)
        c = condorcet_winner(U)
        r = np.random.default_rng(100 + p)
        for method in ('irv', 'plurality'):
            won = set()
            for k, v0 in enumerate(starts(U, method, r)):
                rk = np.random.default_rng(1000 * p + k)
                settled, w, v = run(U, method, v0.copy(), s, rk)
                if not settled:
                    continue
                won.add(w)
                if method == 'irv':
                    f = [v[FIRST == x].sum() for x in range(3)]
                    e = int(np.argmin(f))
                    L, R = w, 3 - w - e
                    b = best_replies(U, v, 'irv', s, 0.002, rk, 6000)
                    for i, u in enumerate(U):
                        order = RANK[b[i]]
                        misordered[1] += 1
                        misordered[0] += (order.index(L) < order.index(R)) != (u[L] > u[R])
            S = stat[method]
            if c is None:
                S['no_cw'] += 1
                S['no_cw_settled'] += bool(won)
            else:
                S['cw'] += 1
                S['none'] += not won
                S['other'] += any(w != c for w in won)
    for method, S in stat.items():
        print(f"{model:8s} s = {s:g}  {method:9s} with a Condorcet winner ({S['cw']} profiles): some "
              f"settled run elects another candidate {S['other']}, no run settles {S['none']}; without "
              f"one ({S['no_cw']}): some run settles {S['no_cw_settled']}")
    print(f"{model:8s} s = {s:g}  IRV best replies at settled polls ranking the finalists against the "
          f"voter's preference: {misordered[0]}/{misordered[1]}")


if __name__ == "__main__":
    if len(sys.argv) > 2:
        main(sys.argv[1], float(sys.argv[2]))
    else:
        for model in ('spatial', 'ic'):
            for s in (85, 20):
                main(model, s)
