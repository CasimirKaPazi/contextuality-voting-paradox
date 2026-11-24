"""Note "A tight form without a rational diagonal", Section 5. Three outcomes:
  Theorem A: without an outcome forced by both players, some player works with Q the reverse or the
  rotation of P;
  Theorem B: with a common veto c, a player has no rational diagonal exactly when (W), (A_a), (A_b),
  (E_ab), (E_ba) hold.
Both are compared with the brute-force test over all strict P, Q: on random forms, and for Theorem B
on all forms with a c-border and inner part 3 x 3, 2 x 4, 3 x 4.  Usage: python3 three_outcomes_veto.py [seed]"""
import itertools, random, sys
ORD = list(itertools.permutations(range(3)))
def T(M): return [list(c) for c in zip(*M)]
def works(A, P, Q):
    C = T(A)
    for r in A:
        y = min(r, key=Q.index)
        if not any(r[j] == y and any(P.index(v) < P.index(y) for v in C[j]) for j in range(len(r))): return False
    return True
def forces(A): return {r[0] for r in A if len(set(r)) == 1}
def no_diag_player(A):            # brute force, all strict P, Q
    return not any(works(A, P, Q) for P in ORD for Q in ORD)
def kinds(A): return any(works(A, P, Q) for P in ORD for Q in (P[::-1], P[1:] + P[:1]))
def cond(A, c):                   # characterisation for a common veto c (A: this player's rows)
    a, b = [u for u in range(3) if u != c]; C = T(A)
    def cells(r, u): return [j for j in range(len(r)) if r[j] == u]
    constc = [all(v == c for v in col) for col in C]
    def A_(x, y):    # (A_x): a row inside {x, c} with its c-cells in columns without x
        return any(set(r) <= {x, c} and all(x not in C[j] for j in cells(r, c)) for r in A)
    def Brow(r): return all(constc[j] for j in cells(r, c))   # wall row
    B = any(Brow(r) for r in A)
    def E_(x, y):    # (E_xy)
        return any(y in r and all(x not in C[j] for j in cells(r, y)) for r in A) or any(y not in r and Brow(r) for r in A)
    return A_(a, b) and A_(b, a) and B and E_(a, b) and E_(b, a)
random.seed(int(sys.argv[1]) if len(sys.argv) > 1 else 1)
n1 = n2 = bad1 = bad2 = cex = 0
for it in range(60000):
    n, m = random.randint(2, 7), random.randint(2, 7)
    M = [[random.randrange(3) for _ in range(m)] for _ in range(n)]
    for _ in range(random.randint(0, n * m)):
        i, j = random.randrange(n), random.randrange(m)
        M[i][j] = M[i][random.randrange(m)] if random.random() < .5 else M[random.randrange(n)][j]
    if random.random() < .6:          # plant a common veto
        c = random.randrange(3); M[random.randrange(n)] = [c] * m
        j = random.randrange(m)
        for r in M: r[j] = c
    if {v for r in M for v in r} != {0, 1, 2}: continue
    fr, fc = forces(M), forces(T(M))
    if fr == {0, 1, 2} or fc == {0, 1, 2}: continue
    common = fr & fc
    if not common:
        n1 += 1; bad1 += not (kinds(M) or kinds(T(M)))
    else:
        c, = common; n2 += 1
        for A in (M, T(M)):
            bad2 += cond(A, c) != no_diag_player(A)
        cex += no_diag_player(M) and no_diag_player(T(M))
print("no common veto:", n1, "forms,", bad1, "without a working configuration of the two kinds")
print("common veto:", n2, "forms,", bad2, "mismatches of the characterisation;", cex, "forms without a rational diagonal")
bad = tot = 0
for n, m in ((3, 3), (2, 4), (3, 4)):
    for cl in itertools.product(range(3), repeat=n * m):
        M = [[2] * (m + 1)] + [[2] + list(cl[i * m:(i + 1) * m]) for i in range(n)]
        if {v for r in M for v in r} != {0, 1, 2}: continue
        for A in (M, T(M)): tot += 1; bad += cond(A, 2) != no_diag_player(A)
print("all forms with a c-border, inner 3 x 3, 2 x 4, 3 x 4:", tot, "player checks,", bad, "mismatches")
