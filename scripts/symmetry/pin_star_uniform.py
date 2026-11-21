"""Star shape with centre a and leaves in a fixed order L: voter ranking = (leaves above a, in
order L), a, (leaves below a, in order L).  Check closure and identification for m = 4..7."""
import itertools, sys
from rankmod import rank_mod
for m in map(int, sys.argv[1:]):
    alts = "abcdefgh"[:m]; leaves = alts[1:]
    R = ["".join(r) for r in itertools.permutations(alts)]
    pos = {r: {x: i for i, x in enumerate(r)} for r in R}
    subs = list(itertools.combinations(alts, m - 1))
    RES = {r: tuple("".join(sorted(T, key=lambda x: pos[r][x])) for T in subs) for r in R}
    W = []
    for pat in itertools.product((0, 1), repeat=m - 1):     # bit 1: a above the leaf
        up = [x for x, b in zip(leaves, pat) if b == 0]; down = [x for x, b in zip(leaves, pat) if b == 1]
        W.append("".join(up) + "a" + "".join(down))
    seen = [set(RES[r][j] for r in W) for j in range(len(subs))]
    closed = sum(all(RES[r][j] in seen[j] for j in range(len(subs))) for r in R) == len(W)
    feats = [(j, o) for j in range(len(subs)) for o in sorted(seen[j])]
    ident = rank_mod([[1 if RES[r][j] == o else 0 for (j, o) in feats] for r in W]) == len(W)
    print(f"m={m} star, same order above and below: {len(W)} rankings, closed {closed}, identified {ident}", flush=True)
