"""Enumerate irreducible totally tight forms (no constant line, no repeated line) of size m x n
with outcomes from range(k) by backtracking, and print them one per line."""
import sys
m, n, k = map(int, sys.argv[1:4])
M = [[None]*n for _ in range(m)]
out = []
def ok_cell(r, c):
    x = M[r][c]
    for r2 in range(r):
        for c2 in range(c):
            A, B, C, D = M[r2][c2], M[r2][c], M[r][c2], x
            if not (A == B or C == D or A == C or B == D): return False
        for c2 in range(c + 1, n):
            pass
    return True
def rec(pos, maxo):
    if pos == m * n:
        rows = [tuple(r) for r in M]; cols = list(zip(*rows))
        if any(len(set(r)) == 1 for r in rows) or any(len(set(c)) == 1 for c in cols): return
        if len(set(rows)) < m or len(set(cols)) < n: return


        print(" ".join("".join(map(str, r)) for r in rows)); return
    r, c = divmod(pos, n)
    for x in range(min(k, maxo + 2)):          # outcomes introduced in order
        M[r][c] = x
        if c == n - 1 and len(set(M[r])) == 1: continue
        if r == m - 1 and len({M[i][c] for i in range(m)}) == 1: continue
        if ok_cell(r, c): rec(pos + 1, max(maxo, x))
    M[r][c] = None
rec(0, -1)
