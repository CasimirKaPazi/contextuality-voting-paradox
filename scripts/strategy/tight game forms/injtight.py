"""Search tight two-person game forms whose rows and columns are injective
(no outcome repeated within a row or a column), with >= 2 rows and columns."""
import sys
from itertools import product, combinations
m1, m2, k = map(int, sys.argv[1:4])
outs = list(range(k))
def tight(rows, cols):
    for r in range(k+1):
        for A in combinations(outs, r):
            A = set(A)
            if not any(set(x) <= A for x in rows) and not any(set(y).isdisjoint(A) for y in cols):
                return False
    return True
found = 0; tot = 0
def rec(cells, pos):
    global found, tot
    if pos == m1*m2:
        used = set(cells)
        if len(used) < 3: return
        # canonical: outcomes appear in order of first occurrence
        rows = [cells[a*m2:(a+1)*m2] for a in range(m1)]
        cols = [tuple(cells[a*m2+c] for a in range(m1)) for c in range(m2)]
        tot += 1
        if tight(rows, cols):
            found += 1
            if found <= 5: print("TIGHT injective:", rows)
        return
    a, c = divmod(pos, m2)
    mx = max(cells) + 1 if cells else 0
    for o in range(min(mx + 1, k)):
        if o in cells[a*m2:pos]: continue                   # row injective
        if any(cells[aa*m2+c] == o for aa in range(a)): continue   # column injective
        rec(cells + [o], pos + 1)
rec([], 0)
print(m1, m2, k, "injective forms (canonical)", tot, "tight among them", found)
