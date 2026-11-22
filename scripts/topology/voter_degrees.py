"""Degrees of voters: Arrow's theorem as a winding (working note *The Global Form*).

Three alternatives. The six rankings form a hexagon, adjacent rankings differing in one comparison.
A voter's loop: one voter walks once around the hexagon while the others stay fixed. Under independence
of irrelevant alternatives (IIA) each step changes only one column, so the social ranking stays put or
moves to a neighbour, and the walk of the outcome has a winding number: the voter's degree at that context.

Part 1: all IIA rules into rankings, for two and three voters (exhaustive). Checks that the degree does
        not depend on the context (the others' rankings, the starting point), that it lies in {-1, 0, 1},
        that the degrees add up to the winding of the diagonal loop (all voters move together), and that a
        voter has non-zero degree exactly when the rule is that voter's dictatorship (degree 1 and
        unanimous) or anti-dictatorship (degree 1, social ranking the reverse of the voter's).
Part 2: rules without IIA (Borda, Copeland, plurality, each with a fixed tie-break). The outcome jumps
        between non-adjacent rankings on many loops, so the winding is not defined there; where it is
        defined it depends on the context.
Part 3: lotteries. The real degree of a voter at a context is the expected winding over a joint draw of
        social rankings along the loop that changes, at each step, at most the comparison the voter
        changes (a section of the loop). For a mixture of dictatorships and anti-dictatorships with weights
        w, the expected winding is pinned to w_i + v_i (dictator plus anti-dictator weight of voter i) by
        the lotteries alone, at every context. The coin rule (three voters; it satisfies only pairwise
        independence and signals across pairs) has sections along every voter's loop, but the expected
        winding is not fixed by its marginals and depends on the context: 1/2 when the other two voters
        agree, 0 when they are two steps apart on the hexagon, anywhere in [0, 1/2] at one step and in
        [0, 1] when they are opposite.
Run: python3 voter_degrees.py   (numpy and scipy)
"""
import itertools
import random
from itertools import permutations, product

import numpy as np
from scipy.optimize import linprog

random.seed(5)
HEX = [(0, 1, 2), (1, 0, 2), (1, 2, 0), (2, 1, 0), (2, 0, 1), (0, 2, 1)]  # cyclic order of rankings
POS = {r: k for k, r in enumerate(HEX)}
PAIRS = [(0, 1), (1, 2), (2, 0)]  # bits (a over b, b over c, c over a); a cycle is all bits equal


def bits(r):
    return tuple(int(r.index(x) < r.index(y)) for x, y in PAIRS)


RANK_OF = {bits(r): r for r in HEX}


def step(a, b):
    """Displacement on the hexagon between consecutive outcomes; None if they are not adjacent."""
    d = (POS[b] - POS[a]) % 6
    return {0: 0, 1: 1, 5: -1}.get(d)


def loop_from(r):
    k = POS[r]
    return [HEX[(k + t) % 6] for t in range(7)]


def winding(outcomes):
    s = 0
    for a, b in zip(outcomes, outcomes[1:]):
        d = step(a, b)
        if d is None:
            return None
        s += d
    assert s % 6 == 0
    return s // 6


# ---------------------------------------------------------------- Part 1: IIA rules into rankings

def iia_rules(n):
    """All triples (f_ab, f_bc, f_ca) of Boolean functions of a column (n bits) whose output is always
    a ranking. Two columns of different pairs can be chosen independently, so the condition is checked
    on all triples of columns that occur together in a profile."""
    cols = list(product((0, 1), repeat=n))
    cidx = {c: i for i, c in enumerate(cols)}
    profs = list(product(HEX, repeat=n))
    occ = sorted({tuple(cidx[tuple(bits(r)[e] for r in p)] for e in range(3)) for p in profs})
    occ = np.array(occ)
    F = np.array(list(product((0, 1), repeat=len(cols))), dtype=np.int8)  # all functions
    rules = []
    nc = len(cols)
    onehot = np.eye(nc, dtype=bool)[occ[:, 2]]          # occurrence -> its ca column
    for fa in range(len(F)):
        va = F[fa][occ[:, 0]]                            # (occ,)
        vb = F[:, occ[:, 1]]                             # (functions, occ)
        eq = vb == va[None, :]
        need0 = (eq & (va[None, :] == 1)) @ onehot       # ca column must be 0
        need1 = (eq & (va[None, :] == 0)) @ onehot       # ca column must be 1
        good = ~np.any(need0 & need1, axis=1)
        for fb in np.nonzero(good)[0]:
            forced = {c: 0 for c in np.nonzero(need0[fb])[0]}
            forced.update({c: 1 for c in np.nonzero(need1[fb])[0]})
            free = [c for c in range(nc) if c not in forced]
            for vals in product((0, 1), repeat=len(free)):
                fc = np.zeros(nc, dtype=np.int8)
                for c, v in forced.items(): fc[c] = v
                for c, v in zip(free, vals): fc[c] = v
                rules.append((F[fa], F[fb], fc))
    return rules, cidx


BITS = {r: bits(r) for r in HEX}


def table(rule, cidx, n):
    """The rule's social ranking at every profile."""
    return {p: RANK_OF[tuple(int(rule[e][cidx[tuple(BITS[r][e] for r in p)]]) for e in range(3))]
            for p in product(HEX, repeat=n)}


def degrees(T, n):
    """Degree of each voter at every context; returns the set of values per voter."""
    out = []
    for i in range(n):
        vals = set()
        for others in product(HEX, repeat=n - 1):
            for start in HEX:
                outs = [T[others[:i] + (r,) + others[i:]] for r in loop_from(start)]
                vals.add(winding(outs))
        out.append(vals)
    return out


def diagonal_winding(T, n, start):
    """All voters at the same ranking, moving together once around."""
    return winding([T[(r,) * n] for r in loop_from(start)])


def kind(T, n):
    for i in range(n):
        if all(T[p] == p[i] for p in T):
            return f"dictator {i}"
        if all(T[p] == p[i][::-1] for p in T):
            return f"anti-dictator {i}"
    return "other"


def part1():
    for n in (2, 3):
        rules, cidx = iia_rules(n)
        tally = {}
        bad = 0
        for rule in rules:
            T = table(rule, cidx, n)
            ds = degrees(T, n)
            if any(len(v) != 1 or None in v for v in ds):
                bad += 1; continue
            d = tuple(next(iter(v)) for v in ds)
            diag = {diagonal_winding(T, n, s) for s in HEX}
            bad += diag != {sum(d)}
            k = kind(T, n)
            bad += (any(d) != (k != "other"))
            tally[(d, k.split()[0])] = tally.get((d, k.split()[0]), 0) + 1
        print(f"Part 1, {n} voters: {len(rules)} IIA rules into rankings; degree not constant, "
              f"or diagonal winding not the sum, or non-zero degree without (anti-)dictatorship: {bad}")
        for (d, k), c in sorted(tally.items()):
            print(f"    degrees {d}: {c} rules ({k})")


# ---------------------------------------------------------------- Part 2: rules without IIA

def borda(prof):
    s = [0, 0, 0]
    for r in prof:
        for k, x in enumerate(r): s[x] += 2 - k
    return tuple(sorted(range(3), key=lambda x: (-s[x], x)))


def copeland(prof):
    s = [0, 0, 0]
    for x, y in itertools.permutations(range(3), 2):
        m = sum(r.index(x) < r.index(y) for r in prof)
        if 2 * m > len(prof): s[x] += 1
    bord = borda(prof)
    return tuple(sorted(range(3), key=lambda x: (-s[x], bord.index(x))))


def plurality(prof):
    s = [0, 0, 0]
    for r in prof: s[r[0]] += 1
    bord = borda(prof)
    return tuple(sorted(range(3), key=lambda x: (-s[x], bord.index(x))))


def part2(trials=3000):
    for name, rule in (("Borda", borda), ("Copeland", copeland), ("plurality", plurality)):
        jumps = 0; values = {}
        for _ in range(trials):
            n = random.randint(2, 7)
            prof = [random.choice(HEX) for _ in range(n)]
            i = random.randrange(n)
            outs = []
            for r in loop_from(prof[i]):
                prof[i] = r; outs.append(rule(prof))
            w = winding(outs)
            if w is None: jumps += 1
            else: values[w] = values.get(w, 0) + 1
        print(f"Part 2, {name}: outcome jumps on {jumps} of {trials} random voter loops; "
              f"windings where defined: {dict(sorted(values.items()))}")


# ---------------------------------------------------------------- Part 3: lotteries along a loop

def closed_walks(start_outcomes):
    """Walks of social rankings along a voter's loop: at step t the voter's comparison on pair e_t
    flips, and the social ranking either stays or flips the same comparison. Closed walks only."""
    walks = []
    for s0 in HEX:
        for flips in product((0, 1), repeat=6):
            w = [s0]; ok = True
            for t, f in enumerate(flips):
                e = start_outcomes[t]
                b = list(bits(w[-1]))
                if f: b[e] ^= 1
                if tuple(b) not in RANK_OF:
                    ok = False; break
                w.append(RANK_OF[tuple(b)])
            if ok and w[-1] == w[0]:
                walks.append(w)
    return walks


def flipped_pair(a, b):
    ba, bb = bits(a), bits(b)
    return next(e for e in range(3) if ba[e] != bb[e])


def section_range(prof_seq, i, constraint):
    """prof_seq: the seven profiles of voter i's loop. Variables: probability of each closed walk."""
    epairs = [flipped_pair(p[i], q[i]) for p, q in zip(prof_seq, prof_seq[1:])]
    walks = closed_walks(epairs)
    A, b = [], []
    for t in range(6):
        kind_, data = constraint(prof_seq[t])
        if kind_ == "lottery":
            for r in HEX:
                A.append([float(w[t] == r) for w in walks]); b.append(data.get(r, 0.0))
        else:
            for e in range(3):
                A.append([float(bits(w[t])[e]) for w in walks]); b.append(data[e])
            A.append([1.0] * len(walks)); b.append(1.0)
    wind = np.array([winding(w) for w in walks], float)
    lo = linprog(wind, A_eq=A, b_eq=b, bounds=[(0, 1)] * len(walks), method="highs")
    hi = linprog(-wind, A_eq=A, b_eq=b, bounds=[(0, 1)] * len(walks), method="highs")
    if lo.status != 0:
        return None
    return lo.fun, -hi.fun


def voter_loop_profiles(prof, i):
    seq = []
    for r in loop_from(prof[i]):
        q = list(prof); q[i] = r; seq.append(tuple(q))
    return seq


def part3(trials=200):
    bad = 0
    for _ in range(trials):
        n = random.randint(2, 5)
        w = np.random.dirichlet(np.ones(2 * n))  # weights of dictators (first n) and anti-dictators
        prof = [random.choice(HEX) for _ in range(n)]
        i = random.randrange(n)

        def lottery(p):
            lot = {}
            for k in range(n):
                lot[p[k]] = lot.get(p[k], 0) + w[k]
                lot[p[k][::-1]] = lot.get(p[k][::-1], 0) + w[n + k]
            return ("lottery", lot)

        lo, hi = section_range(voter_loop_profiles(prof, i), i, lottery)
        bad += abs(lo - (w[i] + w[n + i])) > 1e-7 or abs(hi - (w[i] + w[n + i])) > 1e-7
    print(f"Part 3, mixtures of dictatorships and anti-dictatorships: expected winding of a voter's loop "
          f"differs from the voter's dictator plus anti-dictator weight in {bad} of {trials}")

    # the coin rule, three voters: marginal 1 or 0 on a unanimous pair, 1/2 otherwise
    def coin(p):
        m = []
        for e in range(3):
            s = sum(bits(r)[e] for r in p)
            m.append(1.0 if s == len(p) else 0.0 if s == 0 else 0.5)
        return ("marginals", m)

    by_distance = {}
    none = 0
    for prof in product(HEX, repeat=3):
        res = section_range(voter_loop_profiles(list(prof), 0), 0, coin)
        if res is None:
            none += 1; continue
        d = (POS[prof[2]] - POS[prof[1]]) % 6
        by_distance.setdefault(min(d, 6 - d), set()).add((round(res[0], 6) + 0.0, round(res[1], 6) + 0.0))
    print(f"Part 3, coin rule with three voters, voter 0 at all 216 profiles: no section in {none}; "
          f"range of the expected winding by the hexagon distance of the other two voters: "
          f"{dict(sorted(by_distance.items()))}")


if __name__ == "__main__":
    part1(); part2(); part3()
