"""A tight, non-dictatorial two-player game form with three outcomes in which, for every pair of
strict preferences, both players have a strict Nash strategy (note: A tight form without a
rational diagonal).  Checks, by direct computation on the matrix:
  - all three outcomes occur, the form is tight and nobody is a dictator;
  - every pair of strict preferences has a pure Nash equilibrium (tightness, checked directly);
  - for each player, each P and each Q, the strategy named in the certificate is a strict Nash
    strategy, i.e. a best reply to every best reply of the opponent;
  - deleting any row or column destroys the property (so no smaller form is obtained this way);
  - the form is isomorphic to its transpose.
Outcomes a, b, c; rows are player 1's strategies r0..r5, columns player 2's s0..s5."""
import itertools
FORM = ["cccccc",
        "cbabaa",
        "cbcbbb",
        "cbacca",
        "ccaaaa",
        "cbabcb"]
R = [list(r) for r in FORM]
OUT = "abc"
ORDERS = ["".join(p) for p in itertools.permutations(OUT)]
def T(M): return [list(c) for c in zip(*M)]
def tight(M):
    C = T(M)
    for n in range(1, len(OUT)):
        for S in itertools.combinations(OUT, n):
            S = set(S)
            if not (any(set(r) <= S for r in M) or any(set(c) <= set(OUT) - S for c in C)): return False
    return True
def forces(M): return {r[0] for r in M if len(set(r)) == 1}
def strict_nash(M, P, Q):
    """Strategies (rows of M) of the player with order P that are strict Nash strategies against an
    opponent (columns of M) with order Q: every best reply of the opponent leaves the row a best reply."""
    C = T(M); out = []
    for b, r in enumerate(M):
        y = min(r, key=Q.index)                     # the opponent's favourite outcome in the row
        refuted = any(r[j] == y and any(P.index(v) < P.index(y) for v in C[j]) for j in range(len(r)))
        if not refuted: out.append(b)
    return out
def nash_exists(M, P, Q):
    C = T(M)
    return any(all(P.index(M[a][b]) <= P.index(M[x][b]) for x in range(len(M))) and
               all(Q.index(M[a][b]) <= Q.index(M[a][y]) for y in range(len(M[0])))
               for a in range(len(M)) for b in range(len(M[0])))
def no_diagonal(M):
    if {v for r in M for v in r} != set(OUT) or not tight(M): return False
    if forces(M) == set(OUT) or forces(T(M)) == set(OUT): return False
    return all(strict_nash(A, P, Q) for A in (M, T(M)) for P in ORDERS for Q in ORDERS)
# certificate: (P, Q-condition) -> strategy; Q-condition is a predicate on Q
def cert(P, Q, player):
    rows = {"top_c": 0, "acb": 4, "bca": 2} if player == 0 else {"top_c": 0, "acb": 2, "bca": 1}
    one_c = 1 if player == 0 else 5          # the strategy whose only c is against the constant line
    if P[0] == "c": return rows["top_c"]
    if P in ("acb", "bca"): return rows[P]
    if Q[0] == "c": return one_c
    if Q[0] == P[0]: return one_c            # it holds P's top, which is then the opponent's choice
    if player == 0: return {("abc", "bac"): 4, ("abc", "bca"): 3, ("bac", "abc"): 2, ("bac", "acb"): 5}[P, Q]
    return {("abc", "bac"): 2, ("abc", "bca"): 4, ("bac", "abc"): 1, ("bac", "acb"): 3}[P, Q]
if __name__ == "__main__":
    print("outcomes:", sorted({v for r in R for v in r}), " tight:", tight(R))
    print("forced singletons: player 1", sorted(forces(R)), " player 2", sorted(forces(T(R))))
    print("pure equilibrium for all 36 pairs of strict preferences:", all(nash_exists(R, P, Q) for P in ORDERS for Q in ORDERS))
    ok = True
    for player, M in ((0, R), (1, T(R))):
        for P in ORDERS:
            for Q in ORDERS:
                if cert(P, Q, player) not in strict_nash(M, P, Q): ok = False; print("certificate fails", player, P, Q)
    print("certificate checked for both players, all 36 pairs (P, Q) each:", ok)
    print("no rational diagonal:", no_diagonal(R))
    smaller = [("row", i) for i in range(len(R)) if no_diagonal(R[:i] + R[i + 1:])] + \
              [("column", j) for j in range(len(R[0])) if no_diagonal([r[:j] + r[j + 1:] for r in R])]
    print("deletions that keep the property:", smaller or "none")
    s, t = (0, 2, 4, 5, 3, 1), (0, 5, 1, 4, 2, 3)
    print("transpose = form with rows", s, "and columns", t, ":",
          all(T(R)[i][j] == R[s[i]][t[j]] for i in range(6) for j in range(6)))
