"""Path shape a1-a2-...-am only (enough after the observation that a ranking is the event 'all
consecutive comparisons as in the ranking').  Rule: greedy top-down linear extension of the
voter's pattern for a priority order.  Check closure and identification exactly (mod a prime),
using numpy for speed.  Usage: pin_path_greedy.py m [number of priority orders to try]."""
import itertools, sys, random
import numpy as np
P = 32749
m = int(sys.argv[1]); tries = int(sys.argv[2]) if len(sys.argv) > 2 else 20
alts = "abcdefghijkl"[:m]; S = [(alts[i], alts[i + 1]) for i in range(m - 1)]
subs = list(itertools.combinations(range(m), m - 1))
def greedy(pattern, prio):
    above = {x: set() for x in alts}
    for (u, v), b in zip(S, pattern):
        if b: above[v].add(u)
        else: above[u].add(v)
    rank, left = [], set(alts)
    while left:
        x = min((y for y in left if not (above[y] & left)), key=prio.index)
        rank.append(x); left.remove(x)
    return "".join(rank)
def restr_key(r, T):   # restriction of ranking string r to subset T (indices), as a string
    keep = {alts[i] for i in T}
    return "".join(c for c in r if c in keep)
def rank_mod(A):
    M = np.array(A, dtype=np.int64) % P; rk = 0
    for col in range(M.shape[1]):
        nz = np.nonzero(M[rk:, col])[0]
        if len(nz) == 0: continue
        p = rk + nz[0]; M[[rk, p]] = M[[p, rk]]
        M[rk] = (M[rk] * pow(int(M[rk, col]), P - 2, P)) % P
        f = M[:, col].copy(); f[rk] = 0
        M = (M - np.outer(f, M[rk])) % P
        rk += 1
        if rk == M.shape[0]: break
    return rk
def closure_size(W):
    # rankings all of whose (m-1)-restrictions occur in W: build candidates by inserting the
    # missing alternative into the restrictions to subset 0 and test the others
    seen = [set(restr_key(r, T) for r in W) for T in subs]
    missing0 = alts[[i for i in range(m) if i not in subs[0]][0]]
    cands = set()
    for s in seen[0]:
        for k in range(m):
            cands.add(s[:k] + missing0 + s[k:])
    return sum(all(restr_key(c, T) in seen[j] for j, T in enumerate(subs)) for c in cands), seen
random.seed(0)
pats = list(itertools.product((0, 1), repeat=m - 1))
orders = (sys.argv[3].split(",") if len(sys.argv) > 3 else ["".join(alts)] + ["".join(random.sample(alts, m)) for _ in range(tries - 1)])
for prio in orders:
    W = sorted({greedy(p, prio) for p in pats})
    if len(W) != len(pats): print(prio, "not injective"); continue
    sz, seen = closure_size(W)
    if sz != len(W): print(prio, f"closure {sz} > {len(W)}", flush=True); continue
    feats = [(j, o) for j in range(len(subs)) for o in sorted(seen[j])]
    A = [[1 if restr_key(r, subs[j]) == o else 0 for (j, o) in feats] for r in W]
    rA = rank_mod(A); target = "".join(alts)
    col = [[1 if r == target else 0] for r in W]
    tgt = rank_mod([row + c for row, c in zip(A, col)]) == rA
    print(prio, "closed;", "identified" if rA == len(W) else f"not fully identified (rank {rA} of {len(W)})",
          "; target", "identified" if tgt else "NOT identified", flush=True)
