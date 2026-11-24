"""Faces of the permutohedron and retractions onto them (note *Equivariant
Obstructions*, Section 6.5a).

Rankings of m alternatives are the vertices of the permutohedron; two are
adjacent when they differ by a swap of two neighbours. Checks, for m = 3..6:

1. Faces. A face is an ordered split of the alternatives into blocks, the
   rankings that list the blocks in order; it has the shape of the product of
   the blocks' permutohedra. The 2-faces are hexagons (one block of three) and
   squares (two blocks of two) for every m, counted as C(m,3)(m-2)! and
   C(m,2)C(m-2,2)(m-2)!/2. The facets are the splits into a top set S and the
   rest, 2^m - 2 of them; the 2m with |S| = 1 or m - 1 ("x first", "x last")
   are permutohedra of order m - 1. The "x first" facets are disjoint and
   contain every ranking; each ranking lies in exactly m - 1 facets, one for
   each of its top-k sets.
2. Short walks. For m = 4 every non-backtracking closed walk of at most six
   steps runs once around a 2-face; for m = 5 and 6 there is one that does not
   (in a hexagonal prism).
3. Distances. The graph distance is the number of inversions; the diameter is
   m(m-1)/2 and the reverse is the only ranking at that distance; the largest
   diameter of a proper face is (m-1)(m-2)/2.
4. Retractions. For every face, the map that reorders each block by the
   ranking's relative order of that block, and lists the blocks in order, is
   local (a step goes to a step or to nothing) and fixes the face. Moving a
   candidate x to the top is the case of the facet "x first".

Run: python3 permutohedron_faces.py   (about a second)
"""

import itertools
from math import comb, factorial


def swap(r, i):
    r = list(r)
    r[i], r[i + 1] = r[i + 1], r[i]
    return tuple(r)


def inversions(a, b):
    """Kendall distance between rankings a and b."""
    pos = {c: i for i, c in enumerate(b)}
    seq = [pos[c] for c in a]
    return sum(1 for i, j in itertools.combinations(range(len(seq)), 2)
               if seq[i] > seq[j])


def is_step_or_equal(a, b):
    return a == b or inversions(a, b) == 1


def ordered_splits(m, blocks):
    """All ordered set partitions of range(m) with the given block sizes."""
    def rec(rest, sizes):
        if not sizes:
            yield ()
            return
        for S in itertools.combinations(sorted(rest), sizes[0]):
            for tail in rec(rest - set(S), sizes[1:]):
                yield (S,) + tail
    return list(rec(set(range(m)), list(blocks)))


def face_vertices(split, perms):
    out = []
    for r in perms:
        i, ok = 0, True
        for B in split:
            if set(r[i:i + len(B)]) != set(B):
                ok = False
                break
            i += len(B)
        if ok:
            out.append(r)
    return out


def retract(r, split):
    """Reorder each block by r's relative order, list the blocks in order."""
    out = []
    for B in split:
        out.extend(c for c in r if c in B)
    return tuple(out)


def compositions(m):
    """Ordered block-size sequences summing to m."""
    if m == 0:
        yield ()
        return
    for k in range(1, m + 1):
        for rest in compositions(m - k):
            yield (k,) + rest


def part1(m, perms):
    hexes = sum(len(ordered_splits(m, s)) for s in set(itertools.permutations(
        [3] + [1] * (m - 3))))
    squares = sum(len(ordered_splits(m, s)) for s in set(itertools.permutations(
        [2, 2] + [1] * (m - 4)))) if m >= 4 else 0
    assert hexes == comb(m, 3) * factorial(m - 2)
    assert squares == (comb(m, 2) * comb(m - 2, 2) * factorial(m - 2) // 2
                       if m >= 4 else 0)
    # every 2-face is a hexagon or a square: block sizes with sum(b-1) = 2
    two_face_shapes = {tuple(sorted(c, reverse=True)) for c in compositions(m)
                       if sum(b - 1 for b in c) == 2}
    assert two_face_shapes <= {(3,) + (1,) * (m - 3), (2, 2) + (1,) * (m - 4)}
    facets = [(S,) for k in range(1, m) for S in itertools.combinations(range(m), k)]
    assert len(facets) == 2 ** m - 2
    first = {x: face_vertices(((x,), tuple(c for c in range(m) if c != x)), perms)
             for x in range(m)}
    last = {x: face_vertices((tuple(c for c in range(m) if c != x), (x,)), perms)
            for x in range(m)}
    assert all(len(v) == factorial(m - 1) for v in first.values())
    assert all(len(v) == factorial(m - 1) for v in last.values())
    cover = [r for v in first.values() for r in v]
    assert len(cover) == len(set(cover)) == len(perms)
    for r in perms:
        n = sum(1 for k in range(1, m) for S in itertools.combinations(range(m), k)
                if set(r[:k]) == set(S))
        assert n == m - 1
    return hexes, squares


def is_face_walk(w):
    gens = set(w)
    if len(gens) != 2:
        return False
    i, j = sorted(gens)
    if j == i + 1:
        return len(w) == 6
    return len(w) == 4


def part2(m):
    e = tuple(range(m))
    for L in (4, 6):
        for w in itertools.product(range(m - 1), repeat=L):
            if any(w[k] == w[(k + 1) % L] for k in range(L)):
                continue
            r, seen = e, [e]
            for g in w:
                r = swap(r, g)
                seen.append(r)
            if r != e or len(set(seen[:-1])) != L:
                continue
            if not is_face_walk(w):
                return w
    return None


def part3(m, perms):
    e = tuple(range(m))
    d = {r: inversions(r, e) for r in perms}
    assert max(d.values()) == comb(m, 2)
    assert [r for r in perms if d[r] == comb(m, 2)] == [tuple(reversed(e))]
    # largest proper face diameter: a facet (S, rest) has diameter
    # C(|S|,2) + C(m-|S|,2), largest for |S| = 1 or m - 1
    best = max(comb(k, 2) + comb(m - k, 2) for k in range(1, m))
    assert best == comb(m - 1, 2)
    return best


def part4(m, perms):
    count = 0
    for sizes in compositions(m):
        if len(sizes) == 1:
            continue
        for split in ordered_splits(m, sizes)[:20]:
            face = set(face_vertices(split, perms))
            for r in perms:
                a = retract(r, split)
                assert a in face
                if r in face:
                    assert a == r
                for i in range(m - 1):
                    assert is_step_or_equal(a, retract(swap(r, i), split))
            count += 1
    return count


def main():
    for m in range(3, 7):
        perms = list(itertools.permutations(range(m)))
        hexes, squares = part1(m, perms)
        walk = part2(m) if m <= 6 else None
        diam = part3(m, perms)
        faces = part4(m, perms) if m <= 5 else part4_sample(m, perms)
        print(f"m = {m}: {hexes} hexagons, {squares} squares, 2-faces of no"
              f" other kind; {2 ** m - 2} facets; 'x first' facets partition the"
              f" rankings; diameter {comb(m, 2)} (reverse only), largest face"
              f" diameter {diam}; short closed walk off the faces:"
              f" {walk if walk else 'none'}; retractions local on {faces} faces")


def part4_sample(m, perms):
    """For m = 6, check the retractions on the facets and a sample of faces."""
    count = 0
    splits = []
    for k in range(1, m):
        splits += [(S, tuple(c for c in range(m) if c not in S))
                   for S in itertools.combinations(range(m), k)]
    splits += ordered_splits(m, (4, 1, 1))[:10] + ordered_splits(m, (2, 2, 2))[:10]
    for split in splits:
        face = set(face_vertices(split, perms))
        for r in perms:
            a = retract(r, split)
            assert a in face
            if r in face:
                assert a == r
            for i in range(m - 1):
                assert is_step_or_equal(a, retract(swap(r, i), split))
        count += 1
    return count


if __name__ == "__main__":
    main()
