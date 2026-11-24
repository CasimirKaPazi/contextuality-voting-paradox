"""Local rules for four alternatives (working note *Equivariant Obstructions*, Section 6, "Local rules").

The rankings of four alternatives are the vertices of the permutohedron, whose boundary is a 2-sphere
with 24 vertices, 36 edges (adjacent transpositions), 6 squares and 8 hexagons. A rule is local if one
voter's step moves the social ranking by at most one step, and unanimous if it returns the common ballot
at unanimous profiles.

Part 1, the target. Every closed walk of length at most 6 without backtracking runs around one face,
        so every 2-cell of the profile complex (a face of one voter, or a step of each of two voters)
        has a canonical filling, and a local rule has a degree for each voter. Faces have diameter at
        most 3 and the permutohedron has diameter 6.
Part 2, two voters. Every local unanimous rule of two voters is a dictatorship, with or without Pareto:
        the output is always one of the two ballots, and once it follows voter 2 at (abcd, dcba) it
        follows voter 2 everywhere. The degrees are (1, 0) or (0, 1), and every 3-cell (a face of one
        voter times a step of the other) extends.
Part 3, multiplications. A local map G of two rankings with G(s, abcd) = s and G(abcd, t) = t exists
        for three alternatives (addition on the hexagon) and not for four. For four alternatives the
        obstruction lies in a single 4-cell: on A x B for faces A, B through abcd, such a G exists when
        A = B and not when A and B differ.
Part 4, three voters. A local unanimous rule of three voters with F(s, r0, r0) = s and F(r0, s, r0) = s,
        so with degrees (1, 1, -1), exists for three alternatives (a discrete x y / z) and not for four.
Run: python3 local_rules_m4.py   (numpy and scipy; about fifteen seconds)
"""
import itertools
import time

import numpy as np
from scipy.optimize import Bounds, LinearConstraint, milp
from scipy.sparse import coo_matrix


def permutohedron(m):
    R = list(itertools.permutations(range(m)))
    idx = {r: i for i, r in enumerate(R)}

    def adj(r, s):
        d = [i for i in range(m) if r[i] != s[i]]
        return len(d) == 2 and d[1] == d[0] + 1

    nb = {i: [j for j in range(len(R)) if adj(R[i], R[j])] for i in range(len(R))}
    return R, idx, nb


R4, IDX4, NB4 = permutohedron(4)


def faces4():
    out = []
    for k in (1, 2, 3):
        for A in itertools.combinations(range(4), k):
            B = [x for x in range(4) if x not in A]
            out.append(frozenset(IDX4[a + b] for a in itertools.permutations(A) for b in itertools.permutations(B)))
    return out


FACES = faces4()


def face_name(F):
    v = [R4[i] for i in F]
    k = next(k for k in range(1, 4) if len({frozenset(r[:k]) for r in v}) == 1)
    return "{" + "".join("abcd"[x] for x in sorted(v[0][:k])) + "|" + "".join("abcd"[x] for x in sorted(v[0][k:])) + "}"


# ---------------------------------------------------------------- oriented faces and cellular degrees
_Q, _ = np.linalg.qr(np.array([[1, -1, 0, 0], [0, 1, -1, 0], [0, 0, 1, -1]], float).T)


def _pt(r):
    s = np.zeros(4)
    for pos, x in enumerate(r):
        s[x] = 3 - pos - 1.5
    return _Q.T @ s


_P = np.array([_pt(r) for r in R4])


def _cycle(F):
    F = set(F); c = [min(F)]
    while len(c) < len(F):
        c.append(next(j for j in NB4[c[-1]] if j in F and j not in c))
    return c


OFACES = []
for _F in FACES:
    _c = _cycle(_F)
    _n = sum(np.cross(_P[_c[i]], _P[_c[(i + 1) % len(_c)]]) for i in range(len(_c)))
    OFACES.append(_c if _n @ _P[_c].mean(axis=0) > 0 else _c[::-1])
FACEKEY = {frozenset(c): k for k, c in enumerate(OFACES)}
EDGES4 = [(i, j) for i in range(24) for j in NB4[i] if i < j]


def reduce_walk(w):
    w = list(w)
    while True:
        w = [v for i, v in enumerate(w) if v != w[i - 1]] if len(set(w)) > 1 else w[:1]
        L = len(w)
        hit = next((i for i in range(L) if L > 2 and w[i - 1] == w[(i + 1) % L]), None)
        if hit is None:
            return w
        j = (hit + 1) % L
        w = [w[k] for k in range(L) if k not in (hit, j)]


def walk_chain(w):
    r = reduce_walk(w)
    if len(r) <= 2:
        return {}
    k = FACEKEY[frozenset(r)]
    assert len(r) == len(OFACES[k])
    c = OFACES[k]; i = c.index(r[0])
    return {k: 1 if c[(i + 1) % len(c)] == r[1] else -1}


def addc(a, b, s=1):
    for k, v in b.items():
        a[k] = a.get(k, 0) + s * v


def analyse(F, n):
    """degrees per voter (set over contexts) and number of failing face x edge 3-cells"""
    prof = list(F)
    degs = {}
    for ctx in prof:
        for i in range(n):
            ch = {}
            for c in OFACES:
                addc(ch, walk_chain([F[ctx[:i] + (v,) + ctx[i + 1:]] for v in c]))
            vals = set(ch.values()) | ({0} if len(ch) < 14 else set())
            assert len(vals) == 1
            degs.setdefault(i, set()).add(vals.pop())
    bad = 0

    def sq(i, e1, j, e2, ctx):
        (a, b), (c, d) = e1, e2

        def p(x, y):
            t = list(ctx); t[i] = x; t[j] = y; return F[tuple(t)]
        return walk_chain([p(a, c), p(b, c), p(b, d), p(a, d)])
    for ctx in prof:
        for i in range(n):
            for j in range(n):
                if i == j:
                    continue
                for (c_, d_) in EDGES4:
                    if ctx[j] != c_:
                        continue
                    for fc in OFACES:
                        if ctx[i] != fc[0]:
                            continue
                        ch = {}
                        for k in range(len(fc)):
                            e1 = (fc[k], fc[(k + 1) % len(fc)])
                            if i < j:
                                addc(ch, sq(i, e1, j, (c_, d_), ctx))
                            else:
                                addc(ch, sq(j, (c_, d_), i, e1, ctx), -1)
                        for cv, sgn in ((d_, 1), (c_, -1)):
                            w = []
                            for v in fc:
                                t = list(ctx); t[i] = v; t[j] = cv; w.append(F[tuple(t)])
                            addc(ch, walk_chain(w), sgn)
                        vals = set(ch.values()) | ({0} if len(ch) < 14 else set())
                        bad += vals != {0}
    return {i: sorted(v) for i, v in degs.items()}, bad


# ---------------------------------------------------------------- 0/1 programs for local rules
def local_program(m, profiles, nb, fixed, allowed=None, objective=None):
    """profiles: list of tuples of ranking indices; fixed: dict profile -> ranking; allowed: dict
    profile -> list of rankings; locality along one-voter steps within the profile list."""
    K = len(nb); idx = {p: k for k, p in enumerate(profiles)}; V = len(profiles)
    ub = np.ones(K * V)
    for k, p in enumerate(profiles):
        if p in fixed:
            ub[K * k:K * k + K] = 0; ub[K * k + fixed[p]] = 1
        elif allowed is not None:
            ub[K * k:K * k + K] = 0
            for s in allowed[p]:
                ub[K * k + s] = 1
    rows, cols, vals, lo, hi = [], [], [], [], []
    r = 0
    for k in range(V):
        for s in range(K):
            rows.append(r); cols.append(K * k + s); vals.append(1)
        lo.append(1); hi.append(1); r += 1
    for k, p in enumerate(profiles):
        for i in range(len(p)):
            for v in nb[p[i]]:
                q = p[:i] + (v,) + p[i + 1:]
                if q not in idx or idx[q] < k:
                    continue
                j = idx[q]
                for (a, b) in ((k, j), (j, k)):
                    for s in range(K):
                        rows.append(r); cols.append(K * a + s); vals.append(1)
                        for t in [s] + nb[s]:
                            rows.append(r); cols.append(K * b + t); vals.append(-1)
                        lo.append(-np.inf); hi.append(0); r += 1
    A = coo_matrix((vals, (rows, cols)), shape=(r, K * V)).tocsr()
    c = np.zeros(K * V) if objective is None else objective(profiles, K)
    res = milp(c, constraints=LinearConstraint(A, lo, hi), integrality=np.ones(K * V), bounds=Bounds(0, ub))
    sol = None
    if res.status == 0:
        x = res.x.round().astype(int).reshape(V, K)
        sol = {p: int(np.argmax(x[k])) for k, p in enumerate(profiles)}
    return sol, res


def pareto_allowed(R, profiles):
    m = len(R[0])
    out = {}
    for p in profiles:
        out[p] = [s for s in range(len(R)) if all(
            R[s].index(x) < R[s].index(y) for x in range(m) for y in range(m)
            if x != y and all(R[q].index(x) < R[q].index(y) for q in p))]
    return out


def part1():
    print("Part 1: the permutohedron of four alternatives")
    sizes = sorted(len(F) for F in FACES)
    cyc = set()

    def dfs(path):
        if len(path) > 6:
            return
        for j in NB4[path[-1]]:
            if j == path[0] and len(path) >= 3:
                cyc.add(frozenset(path))
            elif j not in path and j > path[0]:
                dfs(path + [j])
    for v in range(24):
        dfs([v])
    dist = {}
    for s in range(24):
        d = {s: 0}; fr = [s]
        while fr:
            nf = []
            for x in fr:
                for y in NB4[x]:
                    if y not in d:
                        d[y] = d[x] + 1; nf.append(y)
            fr = nf
        dist[s] = d
    diam = max(max(d.values()) for d in dist.values())
    fdiam = max(dist[a][b] for F in FACES for a in F for b in F)
    print(f"  {len(R4)} vertices, {len(EDGES4)} edges, faces of sizes {sizes}")
    print(f"  simple cycles of length <= 6: {len(cyc)}, all of them faces: {all(c in set(FACES) for c in cyc)}")
    print(f"  diameter {diam}; largest diameter of a face {fdiam}")
    print()


def part2():
    print("Part 2: local unanimous rules of two voters")
    prof = list(itertools.product(range(24), repeat=2))
    a, b = IDX4[(0, 1, 2, 3)], IDX4[(3, 2, 1, 0)]
    for pareto in (True, False):
        fixed = {(s, s): s for s in range(24)}
        allowed = pareto_allowed(R4, prof) if pareto else None

        def off(profiles, K):
            c = np.zeros(K * len(profiles))
            for k, p in enumerate(profiles):
                for s in range(K):
                    if s not in p:
                        c[K * k + s] = -1
            return c

        def follow1(profiles, K):
            c = np.zeros(K * len(profiles))
            for k, p in enumerate(profiles):
                if p[0] != p[1]:
                    c[K * k + p[0]] = -1
            return c
        F1, r1 = local_program(4, prof, NB4, fixed, allowed, off)
        F2, r2 = local_program(4, prof, NB4, {**fixed, (a, b): b}, allowed, follow1)
        degs, bad = analyse(F2, 2)
        print(f"  {'with Pareto' if pareto else 'unanimity only'}: most profiles off both ballots"
              f" {int(round(-r1.fun))}; following voter 2 at (abcd, dcba), profiles following voter 1"
              f" {int(round(-r2.fun))}; degrees {degs}; failing 3-cells {bad}")
    print()


def part3():
    print("Part 3: local maps G with G(s, r0) = s and G(r0, t) = t")
    for m in (3, 4):
        R, idx, nb = permutohedron(m)
        r0 = 0
        prof = list(itertools.product(range(len(R)), repeat=2))
        fixed = {}
        for s in range(len(R)):
            fixed[(s, r0)] = s; fixed[(r0, s)] = s
        sol, _ = local_program(m, prof, nb, fixed)
        print(f"  m = {m}: exists {sol is not None}")
    r0 = IDX4[(0, 1, 2, 3)]
    through = [F for F in FACES if r0 in F]
    for A in through:
        row = []
        for B in through:
            prof = [(s, t) for s in A for t in B]
            fixed = {}
            for s in A:
                if (s, r0) in set(prof):
                    fixed[(s, r0)] = s
            for t in B:
                if (r0, t) in set(prof):
                    fixed[(r0, t)] = t
            sol, _ = local_program(4, prof, NB4, fixed)
            row.append(f"{face_name(B)}: {'exists' if sol else 'none'}")
        print(f"  on {face_name(A)} x ...  " + "; ".join(row))
    # the same for the smallest cell by an exact search that does not use the solver
    A = next(F for F in through if face_name(F) == "{ab|cd}")
    B = next(F for F in through if face_name(F) == "{a|bcd}")
    prof = [(s, t) for s in A for t in B]
    nbr = {p: [q for q in prof if q != p and ((q[0] == p[0] and q[1] in NB4[p[1]])
                                              or (q[1] == p[1] and q[0] in NB4[p[0]]))] for p in prof}
    assign = {}
    for s in A:
        assign[(s, r0)] = s
    for t in B:
        assign[(r0, t)] = t
    free = sorted((p for p in prof if p not in assign), key=lambda p: -sum(q in assign for q in nbr[p]))
    nodes = [0]

    def rec(i):
        nodes[0] += 1
        if i == len(free):
            return True
        p = free[i]
        cands = set(range(24))
        for q in nbr[p]:
            if q in assign:
                cands &= {assign[q], *NB4[assign[q]]}
        for v in sorted(cands):
            assign[p] = v
            if rec(i + 1):
                return True
            del assign[p]
        return False
    print(f"  exact search on {{ab|cd}} x {{a|bcd}}: exists {rec(0)} ({nodes[0]} nodes)")
    auts = set()
    for pi in itertools.permutations(range(4)):
        for rev in (0, 1):
            f = tuple(IDX4[tuple(pi[x] for x in (R4[i][::-1] if rev else R4[i]))] for i in range(24))
            assert all(f[j] in NB4[f[i]] for i in range(24) for j in NB4[i])
            auts.add(f)
    print(f"  renamings and reversal: {len(auts)} automorphisms, transitive on rankings:"
          f" {len({f[r0] for f in auts}) == 24}")
    print()


def part4():
    print("Part 4: three voters, F(s, r0, r0) = s and F(r0, s, r0) = s, unanimous, local")
    for m in (3, 4):
        R, idx, nb = permutohedron(m)
        r0 = 0
        prof = list(itertools.product(range(len(R)), repeat=3))
        fixed = {}
        for s in range(len(R)):
            fixed[(s, s, s)] = s; fixed[(s, r0, r0)] = s; fixed[(r0, s, r0)] = s
        t = time.time()
        sol, _ = local_program(m, prof, nb, fixed)
        print(f"  m = {m}: exists {sol is not None}  [{time.time() - t:.0f}s]")
    print()


if __name__ == "__main__":
    part1()
    part2()
    part3()
    part4()
