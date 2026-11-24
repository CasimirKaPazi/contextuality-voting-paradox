"""The sphere of rankings and the simplex of candidates (note *The Global
Form*, Section 3a).

Checks, for m alternatives:

1. Chambers are cones over flags. A utility vector u (coordinate sum zero) is
   the non-negative combination of the centred indicator vectors of its top-k
   sets, k = 1, ..., m-1, with the gaps u_(k) - u_(k+1) as weights. So the
   chamber of a ranking is the cone over the chain top-1 c top-2 c ... of faces
   of the candidate simplex, and the sphere of rankings is the barycentric
   subdivision of the simplex's boundary.
2. Radial projection. The ray from the centre of the simplex in direction u
   leaves the simplex at p_x = (u_x - min u) / sum_y (u_y - min u).
3. Reversal sends the vertex of a set S (S on top, tied) to the vertex of its
   complement.
4. Three alternatives: going once around the hexagon of Section 1 passes the
   three corners and the three edge midpoints of the triangle alternately, so
   the voter loop is the boundary of the triangle traversed once.
5. Score vectors. The score vectors of tournaments on m vertices are exactly
   the lattice points of the permutohedron with vertices the permutations of
   (0, 1, ..., m-1) (Landau's theorem through Rado's majorisation), the
   transitive tournaments going to the vertices; for m = 3 both cyclic
   tournaments go to the centre.
6. Divergence. Summing a row of the pairwise margin matrix gives 2 x Borda
   score - (m - 1); the map kills exactly the cyclic part (the kernel of the
   divergence is the orthogonal complement of the gradients).

Run: python3 candidate_simplex.py   (about a second)
"""

import itertools
import math
import numpy as np

rng = np.random.default_rng(0)


def centred_indicator(S, m):
    v = np.zeros(m)
    v[list(S)] = 1.0
    return v - v.mean()


def part1_2_3():
    for m in range(2, 7):
        for _ in range(500):
            u = rng.normal(size=m)
            u -= u.mean()
            order = np.argsort(-u)
            # 1. cone over the flag of top-k sets
            rec = np.zeros(m)
            for k in range(1, m):
                gap = u[order[k - 1]] - u[order[k]]
                assert gap >= 0
                rec += gap * centred_indicator(order[:k], m)
            assert np.allclose(rec, u)
            # 2. radial projection onto the boundary of the simplex
            p = (u - u.min()) / (u - u.min()).sum()
            d = p - np.ones(m) / m
            assert abs(p.min()) < 1e-12
            assert np.allclose(d / np.linalg.norm(d), u / np.linalg.norm(u))
        # 3. reversal and complements
        for r in range(1, m):
            for S in itertools.combinations(range(m), r):
                T = [x for x in range(m) if x not in S]
                a, b = centred_indicator(S, m), centred_indicator(T, m)
                assert np.allclose(a / np.linalg.norm(a), -b / np.linalg.norm(b))
    print("1-3: chambers are cones over flags; radial projection formula;"
          " reversal = complement (m = 2..6)")


def part4():
    hexagon = ["abc", "bac", "bca", "cba", "cab", "acb"]
    shared = []
    for r, s in zip(hexagon, hexagon[1:] + hexagon[:1]):
        if r[0] == s[0]:
            shared.append("corner " + r[0])
        else:
            assert set(r[:2]) == set(s[:2])
            shared.append("midpoint " + "".join(sorted(r[:2])))
    kinds = [x.split()[0] for x in shared]
    assert kinds == ["midpoint", "corner"] * 3
    assert len(set(shared)) == 6
    print("4: the hexagon passes", ", ".join(shared))


def majorised(x, y):
    xs, ys = sorted(x), sorted(y)
    return sum(x) == sum(y) and all(
        sum(xs[:k]) >= sum(ys[:k]) for k in range(1, len(x)))


def part5():
    for m in range(2, 7):
        pairs = list(itertools.combinations(range(m), 2))
        scores, transitive = set(), {}
        for bits in itertools.product([0, 1], repeat=len(pairs)):
            s = [0] * m
            for (i, j), b in zip(pairs, bits):
                s[i if b else j] += 1
            s = tuple(s)
            scores.add(s)
            if sorted(s) == list(range(m)):
                transitive[s] = transitive.get(s, 0) + 1
        lattice = {x for x in itertools.product(range(m), repeat=m)
                   if majorised(x, list(range(m)))}
        assert scores == lattice
        assert len(transitive) == math.factorial(m)
        assert all(c == 1 for c in transitive.values())
        print(f"5: m = {m}: {len(scores)} score vectors = lattice points of the"
              f" permutohedron; {len(transitive)} vertices, one tournament each")
    # m = 3: the two cyclic tournaments
    for cyc in [((0, 1), (1, 2), (2, 0)), ((1, 0), (2, 1), (0, 2))]:
        s = [0, 0, 0]
        for w, _ in cyc:
            s[w] += 1
        assert s == [1, 1, 1]
    print("5: m = 3: both cyclic tournaments go to the centre (1, 1, 1)")


def part6():
    for m in range(3, 6):
        rankings = list(itertools.permutations(range(m)))
        for _ in range(200):
            shares = rng.dirichlet(np.ones(len(rankings)))
            P = np.zeros((m, m))  # P[x, y] = share ranking x above y
            for w, r in zip(shares, rankings):
                pos = {c: i for i, c in enumerate(r)}
                for x in range(m):
                    for y in range(m):
                        if x != y and pos[x] < pos[y]:
                            P[x, y] += w
            M = P - P.T
            borda = P.sum(axis=1)
            assert np.allclose(M.sum(axis=1), 2 * borda - (m - 1))
        # kernel of the divergence = orthogonal complement of gradients
        pairs = list(itertools.combinations(range(m), 2))
        G = np.zeros((len(pairs), m))  # gradient u -> (u_x - u_y)
        for k, (x, y) in enumerate(pairs):
            G[k, x], G[k, y] = 1, -1
        D = G.T  # divergence of a flow on the pairs
        rank_cyclic = len(pairs) - np.linalg.matrix_rank(D)
        assert rank_cyclic == len(pairs) - (m - 1)
        assert np.allclose(D @ G, m * np.eye(m) - np.ones((m, m)))
    print("6: row sums of margins = 2 Borda - (m - 1); the divergence is the"
          " adjoint of the gradient and its kernel, the cyclic part, has"
          " dimension (m-1)(m-2)/2 (m = 3..5)")


if __name__ == "__main__":
    part1_2_3()
    part4()
    part5()
    part6()
