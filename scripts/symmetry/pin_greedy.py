"""Uniform rule for every shape S: the voter's pattern on S is a partial order; take its greedy
linear extension with respect to a fixed priority order of the alternatives (repeatedly place,
on top, the highest-priority alternative not below any unplaced one; 'top-down'), or the same
from the bottom ('bottom-up').  Check closure and identification for every shape of m-1 pairs
touching all m alternatives, for every priority order."""
import itertools, sys
from rankmod import rank_mod
def shapes(m):
    alts = "abcdefgh"[:m]; pairs = list(itertools.combinations(alts, 2)); out = {}
    for S in itertools.combinations(pairs, m - 1):
        if len({x for p in S for x in p}) < m: continue
        best = min(tuple(sorted(tuple(sorted((alts[pi[alts.index(u)]], alts[pi[alts.index(v)]]))) for u, v in S))
                   for pi in itertools.permutations(range(m)))
        out.setdefault(best, S)
    return alts, list(out.values())
def greedy(alts, S, pattern, prio, mode):
    above = {x: set() for x in alts}      # above[x] = alternatives that must be above x
    for (u, v), b in zip(S, pattern):
        if b: above[v].add(u)
        else: above[u].add(v)
    rank, left = [], set(alts)
    if mode == "top":
        while left:
            x = min((y for y in left if not (above[y] & left)), key=prio.index)
            rank.append(x); left.remove(x)
    else:
        below = {x: {y for y in alts if x in above[y]} for x in alts}
        bottom = []
        while left:
            x = min((y for y in left if not (below[y] & left)), key=prio.index)
            bottom.append(x); left.remove(x)
        rank = bottom[::-1]
    return "".join(rank)
def realizable(alts, S, pattern):
    try:
        above = {x: set() for x in alts}
        for (u, v), b in zip(S, pattern):
            (above[v] if b else above[u]).add(u if b else v)
        left = set(alts)
        while left:
            free = [y for y in left if not (above[y] & left)]
            if not free: return False
            left.remove(free[0])
        return True
    except Exception: return False
if __name__ == "__main__":
    m = int(sys.argv[1]); mode = sys.argv[2]
    alts, shs = shapes(m)
    R = ["".join(r) for r in itertools.permutations(alts)]
    pos = {r: {x: i for i, x in enumerate(r)} for r in R}
    subs = list(itertools.combinations(alts, m - 1))
    RES = {r: tuple("".join(sorted(T, key=lambda x: pos[r][x])) for T in subs) for r in R}
    for S in shs:
        pats = [p for p in itertools.product((0, 1), repeat=m - 1) if realizable(alts, S, p)]
        good = []
        for prio in itertools.permutations(alts):
            W = sorted({greedy(alts, S, p, prio, mode) for p in pats})
            if len(W) != len(pats): continue
            seen = [set(RES[r][j] for r in W) for j in range(len(subs))]
            if sum(all(RES[r][j] in seen[j] for j in range(len(subs))) for r in R) != len(W): continue
            feats = [(j, o) for j in range(len(subs)) for o in sorted(seen[j])]
            if rank_mod([[1 if RES[r][j] == o else 0 for (j, o) in feats] for r in W]) == len(W):
                good.append("".join(prio))
        print(f"m={m} {mode} {' '.join(u+v for u,v in S)}: {len(good)} of {len(list(itertools.permutations(alts)))} priority orders work"
              + (f", e.g. {good[0]}" if good else ""), flush=True)
