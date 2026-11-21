"""Exact certificates for the pinning rules of pin_search.py.

For a rule (pattern of bits on S -> full ranking), let Omega be the set of rankings whose
restriction to every triple occurs among the rule's rankings.  At the completed profile any
social law with the triple marginals of a mixture over the rule's rankings lives on Omega
(whatever the weights, including zero weights).  If the indicator of the event 'bits on S equal
pattern' agrees on Omega with a rational combination of triple-order indicators (plus a
constant), the event's probability is that same combination of triple probabilities, for every
choice of weights; since the mixture itself is such a law, the probability is the mixture's."""
import itertools
from fractions import Fraction as Fr
def solve(A, c):
    """exact solution y of A y = c (any one), or None"""
    m, n = len(A), len(A[0])
    M = [[Fr(x) for x in row] + [Fr(ci)] for row, ci in zip(A, c)]
    piv = []; r = 0
    for col in range(n):
        p = next((i for i in range(r, m) if M[i][col] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        M[r] = [x / M[r][col] for x in M[r]]
        for i in range(m):
            if i != r and M[i][col] != 0:
                f = M[i][col]; M[i] = [a - f * b for a, b in zip(M[i], M[r])]
        piv.append(col); r += 1
    if any(all(x == 0 for x in row[:n]) and row[n] != 0 for row in M): return None
    y = [Fr(0)] * n
    for i, col in enumerate(piv): y[col] = M[i][n]
    return y
alts = "abcd"; R = ["".join(r) for r in itertools.permutations(alts)]
pos = {r: {x: i for i, x in enumerate(r)} for r in R}
triples = list(itertools.combinations(alts, 3))
def bits(r, S): return tuple(int(pos[r][u] < pos[r][v]) for u, v in S)
def restr(r, T): return "".join(sorted(T, key=lambda x: pos[r][x]))
STAR = (("a", "b"), ("a", "c"), ("a", "d")); PATH = (("a", "b"), ("b", "c"), ("c", "d"))
RULES = {
 "star": {(0,0,0):"bcda",(0,0,1):"bcad",(0,1,0):"bdac",(0,1,1):"bacd",(1,0,0):"cdab",(1,0,1):"cabd",(1,1,0):"dabc",(1,1,1):"abcd"},
 "path": {(0,0,0):"dcba",(0,0,1):"cbad",(0,1,0):"bdca",(0,1,1):"bcad",(1,0,0):"adcb",(1,0,1):"acbd",(1,1,0):"abdc",(1,1,1):"abcd"},
}
TARGETS = {"star": (STAR, list(itertools.product((0, 1), repeat=3))),
           "path": (PATH, list(itertools.product((0, 1), repeat=3)))}
for name, rule in RULES.items():
    S, targets = TARGETS[name]
    assert all(bits(r, S) == pt for pt, r in rule.items())
    seen = {T: {restr(r, T) for r in rule.values()} for T in triples}
    Omega = [r for r in R if all(restr(r, T) in seen[T] for T in triples)]
    feats = [(T, o) for T in triples for o in sorted(seen[T])]
    A = [[1] + [1 if restr(r, T) == o else 0 for (T, o) in feats] for r in Omega]
    for pt in targets:
        c = [1 if bits(r, S) == pt else 0 for r in Omega]
        y = solve(A, c)
        assert y is not None and all(sum(a * b for a, b in zip(row, y)) == ci for row, ci in zip(A, c))
        terms = [f"{y[0]}"] + [f"{y[j+1]}*P[{''.join(T)}:{o}]" for j, (T, o) in enumerate(feats) if y[j+1] != 0]
        print(f"{name} {pt}: |Omega|={len(Omega)}  P = " + " + ".join(terms))
print("all certificates verified exactly")

# laws on all sets of three pairs determine a law on the 24 rankings (exact rank)
pairs = list(itertools.combinations(alts, 2))
rows = []
for S3 in itertools.combinations(pairs, 3):
    for pt in itertools.product((0, 1), repeat=3):
        rows.append([1 if bits(r, S3) == pt else 0 for r in R])
def rank(M):
    M = [[Fr(x) for x in row] for row in M]; r = 0
    for col in range(len(M[0])):
        p = next((i for i in range(r, len(M)) if M[i][col] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]
        for i in range(len(M)):
            if i != r and M[i][col] != 0:
                f = M[i][col] / M[r][col]; M[i] = [x - f * y for x, y in zip(M[i], M[r])]
        r += 1
    return r
print("rank of the three-pair marginal map on 24 rankings:", rank(rows))
