"""m alternatives: for every shape of m-1 pairs touching all m alternatives (up to renaming),
search a completion rule whose rankings are closed and identified by the (m-1)-alternative
marginals.  Usage: pinm_search.py m [restarts] [seed]."""
import itertools, random, sys
m = int(sys.argv[1]); restarts = int(sys.argv[2]) if len(sys.argv) > 2 else 300
random.seed(int(sys.argv[3]) if len(sys.argv) > 3 else 0)
P = 1_000_003
alts = "abcdefgh"[:m]; R = ["".join(r) for r in itertools.permutations(alts)]
pos = {r: {x: i for i, x in enumerate(r)} for r in R}
subs = list(itertools.combinations(alts, m - 1))
RES = {r: tuple("".join(sorted(T, key=lambda x: pos[r][x])) for T in subs) for r in R}
def bits(r, S): return tuple(int(pos[r][u] < pos[r][v]) for u, v in S)
def rank_mod(rows):
    M = [[x % P for x in row] for row in rows]; rk = 0
    for col in range(len(M[0])):
        p = next((i for i in range(rk, len(M)) if M[i][col]), None)
        if p is None: continue
        M[rk], M[p] = M[p], M[rk]
        inv = pow(M[rk][col], P - 2, P); M[rk] = [x * inv % P for x in M[rk]]
        for i in range(len(M)):
            if i != rk and M[i][col]:
                f = M[i][col]; M[i] = [(x - f * y) % P for x, y in zip(M[i], M[rk])]
        rk += 1
    return rk
def omega_size(W):
    seen = [set(RES[r][j] for r in W) for j in range(len(subs))]
    return sum(all(RES[r][j] in seen[j] for j in range(len(subs))) for r in R), seen
def shapes():
    pairs = list(itertools.combinations(alts, 2)); out = {}
    for S in itertools.combinations(pairs, m - 1):
        if len({x for p in S for x in p}) < m: continue
        # canonical form up to renaming: sorted degree sequence + component structure via brute force
        best = None
        for pi in itertools.permutations(range(m)):
            mp = {alts[i]: alts[pi[i]] for i in range(m)}
            key = tuple(sorted(tuple(sorted((mp[u], mp[v]))) for u, v in S))
            if best is None or key < best: best = key
        out.setdefault(best, S)
    return list(out.values())
for S in shapes():
    patterns = sorted({bits(r, S) for r in R})
    options = {pt: [r for r in R if bits(r, S) == pt] for pt in patterns}
    found = None
    for _ in range(restarts):
        rule = {pt: random.choice(options[pt]) for pt in patterns}
        score = omega_size(set(rule.values()))[0]
        improved = True
        while improved and score > len(patterns):
            improved = False
            for pt in random.sample(patterns, len(patterns)):
                for r in random.sample(options[pt], min(len(options[pt]), 40)):
                    old = rule[pt]; rule[pt] = r
                    sc = omega_size(set(rule.values()))[0]
                    if sc < score: score = sc; improved = True; break
                    rule[pt] = old
        W = sorted(set(rule.values()))
        sz, seen = omega_size(set(W))
        if sz == len(W) == len(patterns):
            feats = [(j, o) for j in range(len(subs)) for o in sorted(seen[j])]
            A = [[1 if RES[r][j] == o else 0 for (j, o) in feats] for r in W]
            if rank_mod(A) == len(W): found = rule; break
    print(" ".join(u + v for u, v in S), f"{len(patterns)} patterns:", "FOUND" if found else "not found", flush=True)
    if found: print("   ", {"".join(map(str, pt)): r for pt, r in found.items()}, flush=True)
