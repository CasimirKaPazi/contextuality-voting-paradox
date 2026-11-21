"""Theorem 5 for m = 4, 5, 6 alternatives: exact checks of the induction step, from the rules
in pin_rules.json.  For each m:
  (D) a law on the rankings of m alternatives is determined by its marginals on all sets of
      m-1 pairs (full rank of the marginal map, via its Gram matrix, modulo a prime: full rank
      modulo a prime implies full rank over the rationals);
  (P) every set of m-1 pairs that touches all m alternatives is, up to renaming, one of the
      shapes in the file, and its rule satisfies pattern correctness, closure under the
      (m-1)-alternative restrictions, and identification (linear independence over those
      restrictions, again modulo a prime).
Sets of m-1 pairs on fewer alternatives are covered by the case m-1.
Usage: python3 pin_certificate_m.py [m ...]   (default 4 5 6; m = 6 takes some minutes)"""
import itertools, json, sys
import numpy as np
P = 32749
RULES = json.load(open("pin_rules.json"))
def check(m):
    alts = "abcdefgh"[:m]; R = ["".join(r) for r in itertools.permutations(alts)]; n = len(R)
    pos = {r: {x: i for i, x in enumerate(r)} for r in R}
    pairs = list(itertools.combinations(alts, 2))
    def bits(r, S): return tuple(int(pos[r][u] < pos[r][v]) for u, v in S)
    def rank_mod(M):
        M = np.array(M, dtype=np.int64) % P; rk = 0
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
    # (D)
    B = np.array([[int(pos[r][u] < pos[r][v]) for (u, v) in pairs] for r in R], dtype=np.int64)
    G = np.zeros((n, n), dtype=np.int64)
    for S in itertools.combinations(range(len(pairs)), m - 1):
        key = B[:, list(S)] @ (1 << np.arange(m - 1))
        for val in np.unique(key):
            idx = np.nonzero(key == val)[0]; G[np.ix_(idx, idx)] += 1
    rD = rank_mod(G)
    print(f"m={m} (D): rank {rD} of {n}")
    assert rD == n
    # (P)
    subs = list(itertools.combinations(alts, m - 1))
    def restr(r, T): return "".join(sorted(T, key=lambda x: pos[r][x]))
    def canon(S):
        return min(tuple(sorted(tuple(sorted((alts[pi[alts.index(u)]], alts[pi[alts.index(v)]]))) for u, v in S))
                   for pi in itertools.permutations(range(m)))
    have = {canon(tuple((w[0], w[1]) for w in s.split())): s for s in RULES[str(m)]}
    for S in itertools.combinations(pairs, m - 1):
        if len({x for p in S for x in p}) == m:
            assert canon(S) in have, f"missing shape {S}"
    for s, rule in RULES[str(m)].items():
        S = tuple((w[0], w[1]) for w in s.split())
        realizable = {"".join(map(str, bits(r, S))) for r in R}
        assert set(rule) == realizable and all("".join(map(str, bits(r, S))) == pt for pt, r in rule.items())
        W = sorted(set(rule.values())); assert len(W) == len(rule)
        seen = [{restr(r, T) for r in W} for T in subs]
        closed = sorted(r for r in R if all(restr(r, T) in seen[j] for j, T in enumerate(subs))) == W
        feats = [(j, o) for j in range(len(subs)) for o in sorted(seen[j])]
        A = [[1 if restr(r, subs[j]) == o else 0 for (j, o) in feats] for r in W]
        ident = rank_mod(A) == len(W)
        print(f"m={m} (P) {s}: {len(W)} rankings, closure {closed}, identification {ident}")
        assert closed and ident
for m in map(int, sys.argv[1:] or ["4", "5", "6"]):
    check(m)
print("all checks passed")
