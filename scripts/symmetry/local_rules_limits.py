"""Two limits of the methods of Section 6.5a (note *Equivariant
Obstructions*, Section 6.5a, "Where the methods stop").

1. Images of faces. Random local maps from the facet "a first" (a copy of
   the permutohedron of m - 1 alternatives) into the permutohedron of m
   alternatives: some images lie in no proper face, already for m = 4, where
   the closed walks still contract. So degrees of local rules cannot be
   defined through the smallest face containing an image.
2. Three voters. For m = 5 and three voters, the facet constraints (A) and
   (B) of Proposition 14 (from Theorem 16 by retraction) with unanimity and
   arc consistency for locality leave profiles with up to 49 possible values:
   unlike two voters, they do not determine the rule.

Run: python3 local_rules_limits.py           (part 1, about a second)
     python3 local_rules_limits.py three     (adds part 2: about five minutes,
                                              about 0.5 GB of memory)
"""

import itertools
import random
import sys
import numpy as np


def swap(r, i):
    r = list(r)
    r[i], r[i + 1] = r[i + 1], r[i]
    return tuple(r)


def face_images(m, trials, seed=1):
    rng = random.Random(seed)
    P = list(itertools.permutations(range(m)))
    idx = {p: i for i, p in enumerate(P)}
    nbr = [[idx[swap(p, i)] for i in range(m - 1)] for p in P]
    ball = [set([i] + nbr[i]) for i in range(len(P))]
    src = [i for i, p in enumerate(P) if p[0] == 0]
    srcset = set(src)

    def in_proper_face(img):
        return any(len({frozenset(P[i][:k]) for i in img}) == 1 for k in range(1, m))

    escapes, example = 0, None
    for _ in range(trials):
        start = src[rng.randrange(len(src))]
        order, seen, queue = [start], {start}, [start]
        while queue:
            v = queue.pop(0)
            for w in nbr[v]:
                if w in srcset and w not in seen:
                    seen.add(w)
                    order.append(w)
                    queue.append(w)
        val, ok = {}, True
        for v in order:
            cand = set(range(len(P)))
            for w in nbr[v]:
                if w in val:
                    cand &= ball[val[w]]
            if not cand:  # greedy choice ran into a dead end: discard the trial
                ok = False
                break
            val[v] = rng.choice(sorted(cand))
        if not ok:
            continue
        img = set(val.values())
        if not in_proper_face(img):
            escapes += 1
            example = example or sorted(img)
    names = ["".join("abcdef"[c] for c in P[i]) for i in example] if example else []
    print(f"1: m = {m}: {escapes} of {trials} random trials give a local image of a facet in"
          f" no proper face; for example {names[:8]}")
    assert escapes > 0


def three_voters(m=5, n=3):
    P = list(itertools.permutations(range(m)))
    idx = {p: i for i, p in enumerate(P)}
    R = len(P)
    nb = np.array([[idx[swap(p, i)] for i in range(m - 1)] for p in P], dtype=np.int32)

    def inserts(s, x):
        rest = [c for c in s if c != x]
        return [idx[tuple(rest[:k] + [x] + rest[k:])] for k in range(m)]

    D = np.ones((R,) * n + (R,), dtype=bool)
    tops = np.array([p[0] for p in P])
    bottoms = np.array([p[-1] for p in P])
    for x in range(m):
        for ends in (tops, bottoms):
            S = np.where(ends == x)[0]
            for s in S:
                allow = np.zeros(R, dtype=bool)
                allow[inserts(P[s], x)] = True
                D[(s,) + np.ix_(*([S] * (n - 1)))] &= allow
    for r in range(R):
        D[(r,) * n] = False
        D[(r,) * n + (r,)] = True
    chunk = max(1, R // 12)
    while True:
        before = int(D.sum())
        for v in range(n):
            for g in range(m - 1):
                for c0 in range(0, R, chunk):
                    c = slice(c0, min(R, c0 + chunk))
                    Q = D[nb[c, g]] if v == 0 else np.take(D[c], nb[:, g], axis=v)
                    dilated = Q.copy()
                    for h in range(m - 1):
                        dilated |= Q[..., nb[:, h]]
                    D[c] &= dilated
        if int(D.sum()) == before:
            break
    sizes = D.sum(-1)
    print(f"2: m = {m}, {n} voters: after propagation {int(sizes.sum())} possible"
          f" values over {sizes.size} profiles, largest domain {int(sizes.max())}")
    assert sizes.max() > 1


if __name__ == "__main__":
    face_images(4, 20000)
    face_images(5, 20000)
    if len(sys.argv) > 1 and sys.argv[1] == "three":
        three_voters()
