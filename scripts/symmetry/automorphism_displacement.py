"""Automorphisms of the permutohedron that move every ranking by at most one
step (note *Equivariant Obstructions*, Section 6.5a, Lemma 15).

The graph has the rankings of m alternatives as vertices and the swaps of two
neighbours as edges. The script enumerates all its automorphisms (networkx,
VF2), checks that there are 2 m! of them (the renamings, alone and composed
with reversing the positions, as in Feng 2006), and lists those that move
every ranking by at most one step: for m = 3 the identity and the two
rotations of the hexagon by one step, for m = 4 and 5 only the identity. It
also checks the step of the proof that every conjugacy class of permutations
contains one with at most m - 1 inversions.

Run: python3 automorphism_displacement.py     (m = 3, 4, 5; a few seconds)
     python3 automorphism_displacement.py 6   (adds m = 6; about ten minutes)
"""

import itertools
import sys
import networkx as nx
from networkx.algorithms.isomorphism import GraphMatcher


def swap(r, i):
    r = list(r)
    r[i], r[i + 1] = r[i + 1], r[i]
    return tuple(r)


def kendall(a, b):
    pb = {c: i for i, c in enumerate(b)}
    q = [pb[c] for c in a]
    return sum(1 for i in range(len(q)) for j in range(i + 1, len(q)) if q[i] > q[j])


def inversions(p):
    return sum(1 for i in range(len(p)) for j in range(i + 1, len(p)) if p[i] > p[j])


def cycle_type(p):
    seen, out = set(), []
    for i in range(len(p)):
        if i in seen:
            continue
        k, j = 0, i
        while j not in seen:
            seen.add(j)
            j = p[j]
            k += 1
        out.append(k)
    return tuple(sorted(out))


def main(ms):
    for m in ms:
        P = list(itertools.permutations(range(m)))
        G = nx.Graph()
        G.add_nodes_from(P)
        for p in P:
            for i in range(m - 1):
                G.add_edge(p, swap(p, i))
        auts = list(GraphMatcher(G, G).isomorphisms_iter())
        assert len(auts) == 2 * len(P)
        small = [a for a in auts if all(kendall(a[p], p) <= 1 for p in P)]
        nonid = [a for a in small if any(a[p] != p for p in P)]
        # shortest element of every conjugacy class
        shortest = {}
        for p in P:
            ct = cycle_type(p)
            shortest[ct] = min(shortest.get(ct, 10 ** 9), inversions(p))
        assert max(shortest.values()) <= m - 1
        print(f"m = {m}: {len(auts)} automorphisms (= 2 m!); moving every ranking"
              f" at most one step: {len(small)}, of them non-identity {len(nonid)};"
              f" shortest element of each conjugacy class has at most"
              f" {max(shortest.values())} <= m - 1 inversions")
        if m >= 4:
            assert not nonid
        else:
            assert len(nonid) == 2


if __name__ == "__main__":
    extra = [6] if len(sys.argv) > 1 and sys.argv[1] == "6" else []
    main([3, 4, 5] + extra)
