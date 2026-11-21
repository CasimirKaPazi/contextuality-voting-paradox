"""Arrow's problem for three alternatives as a constraint network.

Issues are the three pairs read around the triangle, ab, bc, ca; a ranking is
the triple of bits (a over b, b over c, c over a). The six rankings are exactly
the triples that are not all equal (NAE); the two cycles are 000 and 111.

An aggregator satisfying independence of irrelevant alternatives is a triple
of Boolean functions (f_ab, f_bc, f_ca) of the N voters' bits on each issue.
It is a global solution if, at every profile, the three outputs are not all
equal. Unanimity is idempotence: f(0..0) = 0 and f(1..1) = 1.

The script computes, for N = 2 and 3:
  (a) all unanimous solutions: expected exactly the N dictators (Arrow);
  (b) the solutions with every f symmetric in the voters (anonymous): expected none;
  (c) the fractional assignment f(column) = share of 1s in the column: it is
      always consistent, since the profile itself is a distribution over NAE
      triples with these marginals, and it equals random dictatorship;
      the script checks this and shows the Condorcet profile, where every
      symmetric rounding fails.
"""
from itertools import product, permutations

RANKS = list(permutations("abc"))


def bits(r):
    pos = {x: i for i, x in enumerate(r)}
    return (int(pos["a"] < pos["b"]), int(pos["b"] < pos["c"]), int(pos["c"] < pos["a"]))


TRIPLES = [bits(r) for r in RANKS]
assert sorted(TRIPLES) == sorted(t for t in product((0, 1), repeat=3) if len(set(t)) > 1)


def col_index(column):
    return sum(b << i for i, b in enumerate(column))


def solve(N, symmetric):
    cols = list(product((0, 1), repeat=N))
    allowed = []  # truth tables of candidate functions, as tuples indexed by column
    for table in product((0, 1), repeat=len(cols)):
        if table[col_index((0,) * N)] != 0 or table[col_index((1,) * N)] != 1:
            continue
        if symmetric and any(table[col_index(c)] != table[col_index(tuple(sorted(c)))] for c in cols):
            continue
        allowed.append(table)
    profiles = []
    for prof in product(TRIPLES, repeat=N):
        profiles.append(tuple(col_index(tuple(v[j] for v in prof)) for j in range(3)))
    sols = []
    allowed_set = set(allowed)
    for fab in allowed:
        for fbc in allowed:
            forced = {}
            ok = True
            for cab, cbc, cca in profiles:
                if fab[cab] == fbc[cbc]:
                    need = 1 - fab[cab]
                    if forced.get(cca, need) != need:
                        ok = False
                        break
                    forced[cca] = need
            if not ok:
                continue
            free = [i for i in range(len(cols)) if i not in forced]
            for vals in product((0, 1), repeat=len(free)):
                t = [None] * len(cols)
                for i, v in forced.items():
                    t[i] = v
                for i, v in zip(free, vals):
                    t[i] = v
                t = tuple(t)
                if t in allowed_set:
                    sols.append((fab, fbc, t))
    return cols, sols


def describe(cols, f):
    for k in range(len(cols[0])):
        if all(f[col_index(c)] == c[k] for c in cols):
            return f"voter {k + 1}"
    return "other"


def main():
    for N in (2, 3):
        cols, sols = solve(N, symmetric=False)
        kinds = sorted({tuple(describe(cols, f) for f in s) for s in sols})
        print(f"N={N}: unanimous IIA solutions: {len(sols)}; kinds: {kinds}")
        cols, sym = solve(N, symmetric=True)
        print(f"N={N}: unanimous IIA solutions with all three functions anonymous: {len(sym)}")
    # (c) fractional assignment = random dictatorship
    N = 3
    for prof in product(TRIPLES, repeat=N):
        shares = [sum(v[j] for v in prof) / N for j in range(3)]
        dist = {}
        for v in prof:
            dist[v] = dist.get(v, 0) + 1 / N
        marg = [sum(p * t[j] for t, p in dist.items()) for j in range(3)]
        assert all(abs(a - b) < 1e-12 for a, b in zip(shares, marg))
    print("Fractional assignment (share of 1s on each issue) is realised at every profile "
          "by the profile's own distribution over rankings, i.e. by random dictatorship.")
    prof = [bits(tuple("abc")), bits(tuple("bca")), bits(tuple("cab"))]
    shares = [sum(v[j] for v in prof) / 3 for j in range(3)]
    print("Condorcet profile abc, bca, cab: shares", shares,
          "-> a symmetric rule that treats the three issues alike gives the same bit on all "
          "three (equal shares), which is a cycle; with different rules per issue, (b) still "
          "finds no solution.")


if __name__ == "__main__":
    main()
