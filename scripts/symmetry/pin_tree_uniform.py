"""Recursive rule for tree shapes: block(v) = [block(c) for children c above v, in fixed order],
v, [block(c) for children c below v, in the same order].  Check closure and identification
for every tree shape and every root."""
import itertools, sys
from rankmod import rank_mod
from pin_kernel import tree_shapes
def tree_rule(alts, S, root):
    adj = {x: [] for x in alts}
    for u, v in S: adj[u].append(v); adj[v].append(u)
    children, order = {root: []}, [root]
    for x in order:
        for y in sorted(adj[x]):
            if y not in children: children[y] = []; children[x].append(y); order.append(y)
    out = {}
    for pat in itertools.product((0, 1), repeat=len(S)):
        bit = dict(zip(S, pat))
        def above(c, v):   # is child c above v in the pattern?
            return bit[(v, c)] == 0 if (v, c) in bit else bit[(c, v)] == 1
        def block(v):
            up = "".join(block(c) for c in children[v] if above(c, v))
            dn = "".join(block(c) for c in children[v] if not above(c, v))
            return up + v + dn
        out[pat] = block(root)
    return out
def check(m, rulefun):
    alts, shapes = tree_shapes(m)
    R = ["".join(r) for r in itertools.permutations(alts)]
    pos = {r: {x: i for i, x in enumerate(r)} for r in R}
    subs = list(itertools.combinations(alts, m - 1))
    RES = {r: tuple("".join(sorted(T, key=lambda x: pos[r][x])) for T in subs) for r in R}
    for S in shapes:
        res = []
        for root in alts:
            W = sorted(set(rulefun(alts, S, root).values()))
            seen = [set(RES[r][j] for r in W) for j in range(len(subs))]
            closed = sum(all(RES[r][j] in seen[j] for j in range(len(subs))) for r in R) == len(W)
            feats = [(j, o) for j in range(len(subs)) for o in sorted(seen[j])]
            ident = rank_mod([[1 if RES[r][j] == o else 0 for (j, o) in feats] for r in W]) == len(W)
            res.append(f"{root}:{'C' if closed else '-'}{'I' if ident else '-'}")
        print(f"m={m} {' '.join(u+v for u,v in S)}:", " ".join(res), flush=True)
if __name__ == "__main__":
    for m in map(int, sys.argv[1:]): check(m, tree_rule)
