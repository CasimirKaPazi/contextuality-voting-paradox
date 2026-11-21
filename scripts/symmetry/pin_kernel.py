"""For the symmetric adjacent-insertion rule on tree shapes, compute the combinations of rule
rankings invisible to all (m-1)-alternative marginals, and compare with the parity character
(-1)^(number of 1-bits in the pattern)."""
import itertools, sys, numpy as np
def tree_shapes(m):
    alts = "abcdefgh"[:m]; pairs = list(itertools.combinations(alts, 2)); seen = {}
    for S in itertools.combinations(pairs, m - 1):
        adj = {x: [] for x in alts}
        for u, v in S: adj[u].append(v); adj[v].append(u)
        st, comp = [alts[0]], {alts[0]}
        while st:
            x = st.pop()
            for y in adj[x]:
                if y not in comp: comp.add(y); st.append(y)
        if len(comp) < m: continue
        key = tuple(sorted(tuple(sorted(len(adj[y]) for y in adj[x])) + (len(adj[x]),) for x in alts))
        seen.setdefault(key, S)
    return alts, list(seen.values())
def rule(alts, S, root, last_extreme=False):
    adj = {x: [] for x in alts}
    for u, v in S: adj[u].append(v); adj[v].append(u)
    order, parent = [root], {root: None}
    for x in order:
        for y in sorted(adj[x]):
            if y not in parent: parent[y] = x; order.append(y)
    out = {}
    for pat in itertools.product((0, 1), repeat=len(S)):
        bit = dict(zip(S, pat)); rank = [root]
        for j, y in enumerate(order[1:]):
            x = parent[y]; up = bit[(x, y)] == 0 if (x, y) in bit else bit[(y, x)] == 1
            if last_extreme and j == len(order) - 2: rank.insert(0 if up else len(rank), y)
            else:
                i = rank.index(x); rank.insert(i if up else i + 1, y)
        out[pat] = "".join(rank)
    return out
if __name__ == "__main__":
    m = int(sys.argv[1]); alts, shapes = tree_shapes(m)
    R = ["".join(r) for r in itertools.permutations(alts)]
    pos = {r: {x: i for i, x in enumerate(r)} for r in R}
    subs = list(itertools.combinations(alts, m - 1))
    def restr(r, T): return "".join(sorted(T, key=lambda x: pos[r][x]))
    for S in shapes:
        rl = rule(alts, S, alts[0]); pats = list(rl); W = [rl[p] for p in pats]
        feats = [(T, o) for T in subs for o in sorted({restr(r, T) for r in W})]
        A = np.array([[1.0 if restr(r, T) == o else 0 for (T, o) in feats] for r in W])
        _, sv, V = np.linalg.svd(A.T); rk = int((sv > 1e-9).sum()); K = V[rk:]
        parity = np.array([(-1.0) ** sum(p) for p in pats])
        in_span = np.linalg.matrix_rank(np.vstack([K, parity])) == len(K) if len(K) else False
        print(f"m={m} {' '.join(u+v for u,v in S)}: invisible dimension {len(K)}, parity among them: {in_span}")
