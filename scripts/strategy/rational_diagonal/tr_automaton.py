"""Complete check of the rational diagonal on totally reducible game forms with k outcomes.

A totally reducible two-player form arises from a 1x1 form [z] by repeatedly adding a constant
line (a row or a column filled with one outcome).  For a fixed player i and fixed preferences
(P for i, Q for the opponent), whether i "works" (every row of i has an opponent best reply
that i would leave) depends only on a finite summary: the set of row types (y, M), where y is
the opponent's favourite outcome in the row and M is i's best outcome over the columns where y
sits.  Adding a line updates the summary without looking at the matrix:
  own constant row o : every M becomes max_P(M, o); new type (o, max_P(present + o))
  opponent column o  : rows with o >_Q y become (o, o); others unchanged
Breadth-first search over the joint summaries of all (i, P, Q) therefore covers every
totally reducible form with at most k outcomes, of any size.
"""
import sys
from itertools import permutations
k = int(sys.argv[1]); O = range(k)
prefs = list(permutations(O))
rank = [{x: r for r, x in enumerate(p)} for p in prefs]      # lower rank = better
configs = [(i, a, b) for i in (0, 1) for a in range(len(prefs)) for b in range(len(prefs))]
def maxP(a, x, y): return x if rank[a][x] <= rank[a][y] else y
def bit(y, M): return 1 << (y * k + M)
def types(mask): return [(t // k, t % k) for t in range(k * k) if mask >> t & 1]
def step(state, j, o):
    masks, present, F = state
    present2 = present | (1 << o)
    F2 = list(F)
    F2[1 - j] &= (1 << o)          # opponent's constant lines survive only if equal to o
    F2[j] |= (1 << o)
    new = []
    for (i, a, b), m in zip(configs, masks):
        out = 0
        if j == i:                    # own constant row
            for y, M in types(m): out |= bit(y, maxP(a, M, o))
            best = o
            for x in O:
                if present2 >> x & 1: best = maxP(a, best, x)
            out |= bit(o, best)
        else:                         # opponent's constant column
            for y, M in types(m):
                out |= bit(o, o) if rank[b][o] < rank[b][y] else bit(y, M)
        new.append(out)
    return (tuple(new), present2, tuple(F2))
def valid(state):
    _, present, F = state
    return bin(present).count("1") >= 3 and F[0] != present and F[1] != present
def works(state):
    masks = state[0]
    return [c for c, m in zip(configs, masks)
            if all(rank[c[1]][M] < rank[c[1]][y] for y, M in types(m))]
seen = set(); frontier = []
for z in O:
    s = (tuple(bit(z, z) for _ in configs), 1 << z, (1 << z, 1 << z))
    seen.add(s); frontier.append(s)
bad = 0; nvalid = 0
while frontier:
    nxt = []
    for s in frontier:
        if valid(s):
            nvalid += 1
            if not works(s): bad += 1
        for j in (0, 1):
            for o in O:
                t = step(s, j, o)
                if t not in seen: seen.add(t); nxt.append(t)
    frontier = nxt
print(f"k={k}: {len(seen)} reachable summaries, {nvalid} valid, {bad} without a working config")
