"""Empirical models on a loop of contexts as divisions of finite covers.

A loop has variables x_0, ..., x_{n-1} (indices mod n, n >= 3), finite value
sets V_i, and contexts C_i = {x_i, x_{i+1}} allowing a relation R_i. An
empirical model is a probability distribution e_i on each R_i with equal
marginals on shared variables. The claim checked here (note *Covers and
Division*, Proposition 2; in vertex form, for outcome sets Z_d, a theorem of
Kharoof, Okay and Ipek, arXiv:2406.19961):

    every empirical model is a mixture of closed walks in the layered graph
    of values; a closed walk that winds k times around the loop is a global
    section of the k-fold cover, and its k rotations average to a model
    invariant under the deck group Z/k.

The check: sample vertices of the polytope of empirical models by linear
programming with random objectives, decompose each into cycles of the layered
graph (flow decomposition), and confirm that the cycles reconstruct the model
and that a model of a loop without global section uses only cycles of winding
at least 2, on random loops and on loops built from bijections whose monodromy
has no fixed point. Two named cases: the Liar on a triangle (two "equals", one "is the
negation of"), and the CHSH scenario as a loop of four contexts with all
outcomes allowed, whose 24 vertices should be 16 deterministic boxes
(winding 1) and 8 PR boxes (winding 2).

Run: python3 loop_covers.py   (about half a minute)
"""

import itertools
import numpy as np
from scipy.optimize import linprog

TOL = 1e-9


def model_lp(sizes, rels, c=None):
    """Variables e_i(x, y) for (x, y) in R_i. Returns (index, A_eq, b_eq)."""
    n = len(sizes)
    idx = []
    for i in range(n):
        for (x, y) in rels[i]:
            idx.append((i, x, y))
    pos = {t: k for k, t in enumerate(idx)}
    rows, b = [], []
    for i in range(n):  # each context sums to one
        r = np.zeros(len(idx))
        for (x, y) in rels[i]:
            r[pos[(i, x, y)]] = 1
        rows.append(r)
        b.append(1.0)
    for i in range(n):  # marginal of x_i from C_i equals that from C_{i-1}
        j = (i - 1) % n
        for v in range(sizes[i]):
            r = np.zeros(len(idx))
            for (x, y) in rels[i]:
                if x == v:
                    r[pos[(i, x, y)]] += 1
            for (x, y) in rels[j]:
                if y == v:
                    r[pos[(j, x, y)]] -= 1
            rows.append(r)
            b.append(0.0)
    return idx, np.array(rows), np.array(b)


def random_vertex(sizes, rels, rng):
    idx, A, b = model_lp(sizes, rels)
    if not idx:
        return None
    res = linprog(rng.normal(size=len(idx)), A_eq=A, b_eq=b,
                  bounds=[(0, None)] * len(idx), method="highs")
    if res.status != 0:
        return None
    return {t: w for t, w in zip(idx, res.x) if w > TOL}


def decompose(model, n):
    """Flow decomposition of a model into closed walks of the layered graph.
    Returns a list of (weight, walk), walk a list of (i, x, y) edges."""
    flow = dict(model)
    cycles = []
    while flow:
        (i, x, y) = next(iter(flow))
        node, seen, path = (i, x), {}, []
        while node not in seen:
            seen[node] = len(path)
            li, lx = node
            e = next(t for t in flow if t[0] == li and t[1] == lx)
            path.append(e)
            node = ((li + 1) % n, e[2])
        walk = path[seen[node]:]
        w = min(flow[e] for e in walk)
        for e in walk:
            flow[e] -= w
            if flow[e] <= TOL:
                del flow[e]
        cycles.append((w, walk))
    return cycles


def winding(walk, n):
    assert len(walk) % n == 0
    return len(walk) // n


def descend(cycles, n):
    """The model obtained from the cycles. A walk of winding k with flow w
    passes k times through each context, so it carries mixture weight k*w:
    the descent of the Z/k-average of its k rotations, which puts 1/k on each
    of its k edges in every context. Returns the model and the total weight."""
    out, total = {}, 0.0
    for w, walk in cycles:
        total += winding(walk, n) * w
        for e in walk:
            out[e] = out.get(e, 0) + w
    return out, total


def is_cover_section(walk, n, rels):
    """A closed walk of winding k is a global section of the k-fold cover:
    consecutive edges agree on the shared variable and each lies in R_i."""
    for a, b in zip(walk, walk[1:] + walk[:1]):
        if b[0] != (a[0] + 1) % n or b[1] != a[2]:
            return False
    return all((x, y) in rels[i] for (i, x, y) in walk)


def has_global_section(sizes, rels):
    n = len(sizes)
    for xs in itertools.product(*[range(s) for s in sizes]):
        if all((xs[i], xs[(i + 1) % n]) in rels[i] for i in range(n)):
            return True
    return False


def check_vertices(sizes, rels, rng, samples):
    n = len(sizes)
    section = has_global_section(sizes, rels)
    vertices = {}
    for _ in range(samples):
        v = random_vertex(sizes, rels, rng)
        if v is None:
            return None
        key = tuple(sorted((t, round(w, 6)) for t, w in v.items()))
        vertices[key] = v
    windings = []
    for v in vertices.values():
        cyc = decompose(v, n)
        rec, total = descend(cyc, n)
        assert abs(total - 1) < 1e-7
        assert set(rec) == set(v)
        assert all(abs(rec[t] - v[t]) < 1e-7 for t in v)
        assert all(is_cover_section(walk, n, rels) for _, walk in cyc)
        ks = [winding(walk, n) for _, walk in cyc]
        if not section:
            assert min(ks) >= 2, "a cycle of winding 1 would be a section"
        windings.append(tuple(sorted(ks)))
    return section, windings


def liar_triangle():
    eq = {(0, 0), (1, 1)}
    neq = {(0, 1), (1, 0)}
    return [2, 2, 2], [eq, eq, neq]


def chsh():
    full = set(itertools.product(range(2), range(2)))
    return [2, 2, 2, 2], [full] * 4


def main():
    rng = np.random.default_rng(1)

    sizes, rels = liar_triangle()
    section, ws = check_vertices(sizes, rels, rng, 200)
    print("Liar triangle: global section:", section,
          "| vertex windings:", sorted(set(ws)))

    sizes, rels = chsh()
    section, ws = check_vertices(sizes, rels, rng, 4000)
    count = {}
    for w in ws:
        count[w] = count.get(w, 0) + 1
    print("CHSH loop: vertices found:", len(ws), "| by windings:", count)
    assert count.get((1,), 0) == 16 and count.get((2,), 0) == 8

    # Loops of bijections with a perturbation: the monodromy of the
    # bijections is a permutation without fixed point, and extra pairs are
    # added at random as long as no global section appears.
    planted, maxk_p = 0, 1
    while planted < 60:
        n = int(rng.integers(3, 6))
        m = int(rng.integers(2, 6))
        perms = [rng.permutation(m) for _ in range(n)]
        mono = np.arange(m)
        for p in perms:
            mono = p[mono]
        if np.any(mono == np.arange(m)):
            continue
        rels = [{(x, int(p[x])) for x in range(m)} for p in perms]
        for _ in range(int(rng.integers(0, 4))):
            i = int(rng.integers(n))
            extra = (int(rng.integers(m)), int(rng.integers(m)))
            rels[i].add(extra)
            if has_global_section([m] * n, rels):
                rels[i].discard(extra)
        out = check_vertices([m] * n, rels, rng, 30)
        assert out is not None and not out[0]
        planted += 1
        maxk_p = max(maxk_p, max(max(w) for w in out[1]))
    print("planted loops without global section:", planted,
          "| largest winding at a vertex:", maxk_p)

    tested, contextual, maxk = 0, 0, 1
    for trial in range(400):
        n = int(rng.integers(3, 6))
        sizes = [int(rng.integers(2, 5)) for _ in range(n)]
        rels = []
        for i in range(n):
            pairs = [(x, y) for x in range(sizes[i])
                     for y in range(sizes[(i + 1) % n])]
            keep = rng.random(len(pairs)) < 0.45
            rels.append({p for p, k in zip(pairs, keep) if k})
        out = check_vertices(sizes, rels, rng, 30)
        if out is None:
            continue
        section, ws = out
        tested += 1
        if not section:
            contextual += 1
        maxk = max(maxk, max(max(w) for w in ws))
    print("random loops with a model:", tested,
          "| without global section:", contextual,
          "| largest winding at a vertex:", maxk)
    print("all decompositions reconstruct the model; all cycles are cover"
          " sections; no winding-1 cycle where the loop has no section")


if __name__ == "__main__":
    main()
