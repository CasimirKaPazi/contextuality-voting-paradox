"""Independent check of the finite facts behind Theorem 5′ (Four Levels), for m = 4, 5, 6.

Written separately from pin_certificate_m.py; it reads only the rules in pin_rules.json.
For each m it checks:
  (a) coverage: every set of m-1 pairs that touches all m alternatives is, up to renaming
      the alternatives, the shape of one of the rules (shapes compared as edge sets in a
      canonical labelling, by brute force over all relabellings);
  (b) for each rule: every pattern maps to a ranking with that pattern, and the patterns of
      the rule are exactly those realised by some ranking; closure (every ranking whose
      restrictions to all (m-1)-element sets of alternatives occur among those of W lies
      in W); identification (the restriction matrix of W has full column rank, computed in
      floating point and exactly modulo 1000003);
  (c) determination: the marginal map on sets of m-1 pairs has full rank m!, computed as
      the rank of its Gram matrix, in floating point and exactly modulo 1000003.
Usage: python3 pin_independent_check.py   (run from this folder; a few seconds)
"""
import itertools
import json
import numpy as np

PR = 1000003


def rank_mod(M, p=PR):
    """Exact rank modulo p of an integer matrix (entries below p), by vectorised elimination."""
    A = np.array(M, dtype=np.int64) % p
    rows, cols = A.shape
    r = 0
    for c in range(cols):
        if r == rows:
            break
        nz = np.nonzero(A[r:, c])[0]
        if len(nz) == 0:
            continue
        i = r + nz[0]
        A[[r, i]] = A[[i, r]]
        A[r] = (A[r] * pow(int(A[r, c]), p - 2, p)) % p
        f = A[:, c].copy()
        f[r] = 0
        A = (A - np.outer(f, A[r])) % p
        r += 1
    return r


def canon(S, m):
    best = None
    for perm in itertools.permutations(range(m)):
        e = tuple(sorted(tuple(sorted((perm[u], perm[v]))) for u, v in S))
        if best is None or e < best:
            best = e
    return best


def main():
    rules = json.load(open("pin_rules.json"))
    ok_all = True
    for m in (4, 5, 6):
        alts = "abcdefgh"[:m]
        idx = {a: i for i, a in enumerate(alts)}
        R = ["".join(r) for r in itertools.permutations(alts)]
        pos = {r: {x: i for i, x in enumerate(r)} for r in R}
        pairs = list(itertools.combinations(range(m), 2))

        shapes = set()
        for S in itertools.combinations(pairs, m - 1):
            if len({v for e in S for v in e}) == m:
                shapes.add(canon(S, m))
        rule_shapes = {}
        for key, rule in rules[str(m)].items():
            S = [(idx[p[0]], idx[p[1]]) for p in key.split()]
            rule_shapes[canon(S, m)] = (S, rule)
        covered = shapes <= set(rule_shapes)
        ok_all &= covered
        print(f"m={m}: {len(shapes)} shapes touching all alternatives, {len(rule_shapes)} rules, covered: {covered}")

        subsets = list(itertools.combinations(alts, m - 1))

        def restr(r, T):
            return "".join(c for c in r if c in T)

        def pattern(r, S):
            return "".join("1" if pos[r][alts[u]] < pos[r][alts[v]] else "0" for u, v in S)

        for S, rule in rule_shapes.values():
            W = set(rule.values())
            pat_ok = all(pattern(r, S) == pat for pat, r in rule.items())
            pat_ok &= {pattern(r, S) for r in R} == set(rule)
            rs = {T: {restr(w, T) for w in W} for T in subsets}
            closure = {r for r in R if all(restr(r, T) in rs[T] for T in subsets)} == W
            Wl = sorted(W)
            M = [[1 if restr(w, T) == o else 0 for w in Wl] for T in subsets for o in sorted(rs[T])]
            ident = (np.linalg.matrix_rank(np.array(M, float)) == len(Wl)) and rank_mod(M) == len(Wl)
            ok_all &= pat_ok and closure and ident
            name = " ".join(alts[u] + alts[v] for u, v in S)
            print(f"   {name}: |W| = {len(W)}, patterns {pat_ok}, closure {closure}, identification {ident}")

        G = np.zeros((len(R), len(R)), np.int64)
        for S in itertools.combinations(pairs, m - 1):
            classes = {}
            for j, r in enumerate(R):
                classes.setdefault(pattern(r, S), []).append(j)
            for cl in classes.values():
                G[np.ix_(cl, cl)] += 1
        rf = np.linalg.matrix_rank(G.astype(float))
        rp = rank_mod(G)
        ok_all &= rf == len(R) and rp == len(R)
        print(f"   determination: Gram rank {rf} (floating point), {rp} (mod {PR}) of {len(R)}")
    print("all checks passed" if ok_all else "SOME CHECK FAILED")


if __name__ == "__main__":
    main()
