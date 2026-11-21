"""Complexes of strict comparisons on n alternatives and their quotients by reversal.

K_n   : simplices are the sets of comparisons x > y contained in a single strict
        order (equivalently: acyclic sets, no comparison together with its reverse).
        For n = 3 this is the six-triangle annulus of Livson, Pritam and Prokopenko.
P_n   : simplices are all sets of comparisons containing no comparison together with
        its reverse (partial tournaments): the boundary of the cross-polytope in
        dimension C(n,2). For n = 3 this is the "realised case", the octahedron.

Reversal r sends x > y to y > x. It is a free simplicial involution on both
complexes (no simplex contains a comparison and its reverse). The quotient chain
complex has one cell per orbit of simplices; the sign of r on an oriented simplex
is the parity of the permutation that re-sorts its image.

Printed for each complex and each field F (GF(2), GF(3), GF(p) with p large):
reduced Betti numbers of the complex and Betti numbers of the quotient.

Expected (Section 5 of Cycles and Twists, "More alternatives"):
  K_n ~ S^(n-2), with r acting as the antipodal map (degree (-1)^(n-1));
  P_n = S^(C(n,2)-1), r antipodal; quotients have the homology of RP^(n-2)
  and RP^(C(n,2)-1).  Over a field of odd characteristic the quotient has a top
  class exactly when r preserves orientation of the sphere.
For n = 3 the script also checks that K_3 / r is a Moebius strip.
For n <= 4 it tests whether K_n is a homology manifold with boundary: K_3 is
(the annulus); K_4 fails exactly at the eight sets in which one alternative
beats, or is beaten by, all others, whose link is a copy of K_3.
"""

from itertools import combinations, permutations
import sys

LARGE_P = 1_000_003


def comparisons(n):
    return [(x, y) for x in range(n) for y in range(n) if x != y]


def complex_K(n):
    comps = comparisons(n)
    index = {c: i for i, c in enumerate(comps)}
    faces = set()
    for order in permutations(range(n)):
        pos = {a: i for i, a in enumerate(order)}
        facet = [index[(x, y)] for (x, y) in comps if pos[x] < pos[y]]
        for k in range(1, len(facet) + 1):
            for s in combinations(facet, k):
                faces.add(s)
    return comps, index, faces


def complex_P(n):
    comps = comparisons(n)
    index = {c: i for i, c in enumerate(comps)}
    pairs = [(x, y) for x in range(n) for y in range(x + 1, n)]
    faces = set()
    # each pair: absent, x>y, or y>x
    from itertools import product
    for choice in product((0, 1, 2), repeat=len(pairs)):
        s = []
        for (x, y), c in zip(pairs, choice):
            if c == 1:
                s.append(index[(x, y)])
            elif c == 2:
                s.append(index[(y, x)])
        if s:
            faces.add(tuple(sorted(s)))
    return comps, index, faces


def reversal_map(comps, index):
    return [index[(y, x)] for (x, y) in comps]


def sort_sign(seq):
    """Return (sorted tuple, sign of the sorting permutation)."""
    arr = list(seq)
    sign = 1
    # insertion sort counting transpositions
    for i in range(1, len(arr)):
        j = i
        while j > 0 and arr[j - 1] > arr[j]:
            arr[j - 1], arr[j] = arr[j], arr[j - 1]
            sign = -sign
            j -= 1
    return tuple(arr), sign


def rank_mod_p(rows, p):
    """Rank of a sparse matrix over GF(p); rows are dicts col -> value."""
    pivots = {}  # pivot col -> row (dict), normalised so pivot entry is 1
    rank = 0
    for row in rows:
        r = {c: v % p for c, v in row.items() if v % p}
        while r:
            c = min(r)
            if c in pivots:
                f = r[c]
                for cc, vv in pivots[c].items():
                    nv = (r.get(cc, 0) - f * vv) % p
                    if nv:
                        r[cc] = nv
                    else:
                        r.pop(cc, None)
            else:
                inv = pow(r[c], p - 2, p)
                pivots[c] = {cc: (vv * inv) % p for cc, vv in r.items()}
                rank += 1
                break
    return rank


def rank_mod_2(rows):
    pivots = {}
    rank = 0
    for row in rows:
        r = 0
        for c, v in row.items():
            if v % 2:
                r ^= 1 << c
        while r:
            c = r.bit_length() - 1
            if c in pivots:
                r ^= pivots[c]
            else:
                pivots[c] = r
                rank += 1
                break
    return rank


def rank(rows, p):
    return rank_mod_2(rows) if p == 2 else rank_mod_p(rows, p)


def chain_complex(faces):
    by_dim = {}
    for s in faces:
        by_dim.setdefault(len(s) - 1, []).append(s)
    for d in by_dim:
        by_dim[d].sort()
    idx = {d: {s: i for i, s in enumerate(by_dim[d])} for d in by_dim}
    bnd = {}
    for d in by_dim:
        if d == 0:
            continue
        rows = []
        for s in by_dim[d]:
            row = {}
            for i in range(len(s)):
                t = s[:i] + s[i + 1:]
                row[idx[d - 1][t]] = row.get(idx[d - 1][t], 0) + (-1) ** i
            rows.append(row)
        bnd[d] = rows
    dims = {d: len(by_dim[d]) for d in by_dim}
    return dims, bnd


def quotient_chain_complex(faces, rmap):
    """Cells = orbits {s, r(s)}; representative = lexicographically smaller."""
    rep = {}
    for s in faces:
        img, sg = sort_sign([rmap[v] for v in s])
        if s <= img:
            rep[s] = (s, 1)
            rep[img] = (s, sg)  # [img] = sg * [s]  (r is an involution)
    # consistency: for img the sign of r(img) -> s is the same sg
    reps = sorted({v[0] for v in rep.values()})
    by_dim = {}
    for s in reps:
        by_dim.setdefault(len(s) - 1, []).append(s)
    idx = {d: {s: i for i, s in enumerate(by_dim[d])} for d in by_dim}
    bnd = {}
    for d in by_dim:
        if d == 0:
            continue
        rows = []
        for s in by_dim[d]:
            row = {}
            for i in range(len(s)):
                t = s[:i] + s[i + 1:]
                tr, sg = rep[t]
                j = idx[d - 1][tr]
                row[j] = row.get(j, 0) + sg * (-1) ** i
            rows.append(row)
        bnd[d] = rows
    dims = {d: len(by_dim[d]) for d in by_dim}
    return dims, bnd


def betti(dims, bnd, p, reduced):
    top = max(dims)
    ranks = {d: rank(bnd[d], p) for d in bnd}
    out = []
    for d in range(top + 1):
        b = dims.get(d, 0) - ranks.get(d, 0) - ranks.get(d + 1, 0)
        if d == 0 and reduced:
            b -= 1
        out.append(b)
    return out


def moebius_check(faces, rmap):
    """For K_3: quotient is a surface with boundary; report boundary circles,
    Euler characteristic and orientability (via GF(p) relative top homology)."""
    dims, bnd = quotient_chain_complex(faces, rmap)
    chi = sum((-1) ** d * k for d, k in dims.items())
    # edge degrees in the quotient
    deg = [0] * dims[1]
    for row in bnd[2]:
        for j in row:
            deg[j] += 1
    boundary_edges = sum(1 for k in deg if k == 1)
    interior_edges = sum(1 for k in deg if k == 2)
    # orientable iff there is a 2-chain with integer +-1 coefficients whose
    # boundary avoids all interior edges; over GF(p) odd, check H_2(Q, dQ):
    interior = [j for j, k in enumerate(deg) if k == 2]
    rows = [{c: v for c, v in row.items() if c in interior} for row in bnd[2]]
    r = rank_mod_p(rows, LARGE_P)
    orientable = (dims[2] - r) > 0
    return chi, boundary_edges, interior_edges, orientable


def link(faces, s):
    ss = set(s)
    return {tuple(sorted(set(t) - ss)) for t in faces if ss < set(t)}


def manifold_check(faces):
    """Homology-manifold test: the link of every k-face of a pure d-complex must
    have the homology of S^(d-k-1) or of a point (over GF(2) and GF(p)).
    Returns the faces that fail, with the reduced Betti numbers of their links."""
    d = max(len(s) for s in faces) - 1
    bad = []
    for s in faces:
        k = len(s) - 1
        if k == d:
            continue  # link empty: the (-1)-sphere
        L = link(faces, s)
        dims, bnd = chain_complex(L)
        res = []
        for p in (2, LARGE_P):
            b = betti(dims, bnd, p, True)
            b += [0] * (d - k - len(b))
            res.append(tuple(b))
        sphere = tuple(1 if i == d - k - 1 else 0 for i in range(d - k))
        ball = tuple(0 for _ in range(d - k))
        if not all(b == sphere for b in res) and not all(b == ball for b in res):
            bad.append((s, res[0]))
    return bad


def main():
    ns = [int(a) for a in sys.argv[1:]] or [3, 4, 5]
    fields = [2, 3, LARGE_P]
    for n in ns:
        comps, index, faces = complex_K(n)
        rmap = reversal_map(comps, index)
        dims, bnd = chain_complex(faces)
        qdims, qbnd = quotient_chain_complex(faces, rmap)
        print(f"K_{n}: f-vector {[dims[d] for d in sorted(dims)]}")
        for p in fields:
            print(f"  GF({p}): reduced Betti of K_{n} {betti(dims, bnd, p, True)};"
                  f" Betti of K_{n}/r {betti(qdims, qbnd, p, False)}")
        if n == 3:
            chi, be, ie, ori = moebius_check(faces, rmap)
            print(f"  K_3/r: Euler characteristic {chi}, {be} boundary edges,"
                  f" {ie} interior edges, orientable: {ori}")
        if n <= 4:
            bad = manifold_check(faces)
            names = [", ".join(f"{comps[v][0]}>{comps[v][1]}" for v in s)
                     for s, _ in bad]
            print(f"  K_{n} homology manifold (with boundary): {not bad};"
                  f" failing faces: {len(bad)}")
            for s, b in zip(names, bad):
                print(f"    {{{s}}}: link has reduced Betti {list(b[1])}")
        if n <= 4:
            comps, index, faces = complex_P(n)
            rmap = reversal_map(comps, index)
            dims, bnd = chain_complex(faces)
            qdims, qbnd = quotient_chain_complex(faces, rmap)
            print(f"P_{n}: f-vector {[dims[d] for d in sorted(dims)]}")
            for p in fields:
                print(f"  GF({p}): reduced Betti of P_{n} {betti(dims, bnd, p, True)};"
                      f" Betti of P_{n}/r {betti(qdims, qbnd, p, False)}")


if __name__ == "__main__":
    main()
