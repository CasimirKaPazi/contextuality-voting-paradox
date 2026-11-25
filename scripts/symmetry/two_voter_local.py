"""Two-voter local unanimous rules are dictatorships: an independent check of
Proposition 14 for five and six alternatives (note *Equivariant
Obstructions*, Section 6.5a; the proof there is by hand, for every m).

A two-voter rule F(s, t) on rankings of m alternatives is local if a step of
either voter moves the social ranking by at most one step, and unanimous if
F(s, s) = s. For m - 1 alternatives assume that every such rule is a
dictatorship (for m - 1 = 4 this is computed in `local_rules_m4.py`). Then, by
Lemma 11 and the argument of Proposition 14, one voter, say voter 1, is the
dictator of the retracted rule on every facet "x first" and "x last":

    (A) if s and t both rank x first, F(s, t) ranks the others as s does;
    (B) if s and t both rank y last, likewise for the others than y.

This script imposes (A), (B) and unanimity on the domains of all m!^2
profiles and runs arc consistency for locality (each domain is cut down to
the rankings within one step of the domain of every neighbouring profile)
until nothing changes. The method is sound: every rule satisfying the
constraints survives. For m = 5 and m = 6 every domain ends as the single
ranking s, so F(s, t) = s: the rule is voter 1's dictatorship.

Run: python3 two_voter_local.py 5   (under a second)
     python3 two_voter_local.py 6   (about six minutes, about 0.5 GB of memory)
"""

import itertools
import sys
import time
import numpy as np


def main(m):
    P = list(itertools.permutations(range(m)))
    idx = {p: i for i, p in enumerate(P)}
    N = len(P)

    def swap(r, i):
        r = list(r)
        r[i], r[i + 1] = r[i + 1], r[i]
        return tuple(r)

    nb = np.array([[idx[swap(p, i)] for i in range(m - 1)] for p in P],
                  dtype=np.int32)

    def inserts(s, x):
        """s with x moved to any position: the rankings that order the others as s."""
        rest = [c for c in s if c != x]
        return {idx[tuple(rest[:k] + [x] + rest[k:])] for k in range(m)}

    D = np.ones((N, N, N), dtype=bool)  # D[s, t, r]: F(s, t) = r still possible
    for si, s in enumerate(P):
        top, bottom = inserts(s, s[0]), inserts(s, s[-1])
        for ti, t in enumerate(P):
            allowed = None
            if s[0] == t[0]:
                allowed = set(top)
            if s[-1] == t[-1]:
                allowed = allowed & bottom if allowed is not None else set(bottom)
            if allowed is not None:
                row = np.zeros(N, dtype=bool)
                row[list(allowed)] = True
                D[si, ti] &= row
        D[si, si] = False
        D[si, si, si] = True

    chunk = max(1, N // 12)
    rounds = 0
    while True:
        rounds += 1
        before = int(D.sum())
        t0 = time.time()
        for voter in (0, 1):
            for g in range(m - 1):
                for c0 in range(0, N, chunk):
                    c = slice(c0, min(N, c0 + chunk))
                    Q = D[nb[c, g]] if voter == 0 else D[c][:, nb[:, g], :]
                    dilated = Q.copy()
                    for h in range(m - 1):
                        dilated |= Q[..., nb[:, h]]
                    D[c] &= dilated
        after = int(D.sum())
        print(f"round {rounds}: {before} -> {after} possible values"
              f" ({time.time() - t0:.1f} s)", flush=True)
        if after == before:
            break

    sizes = D.sum(axis=2)
    assert (sizes == 1).all(), "some profile is not determined"
    s_idx = np.arange(N)[:, None].repeat(N, axis=1)
    t_idx = np.arange(N)[None, :].repeat(N, axis=0)
    assert D[s_idx, t_idx, s_idx].all()
    print(f"m = {m}: every profile (s, t) has the single possible value s;"
          f" the rule is voter 1's dictatorship")


if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 5)
