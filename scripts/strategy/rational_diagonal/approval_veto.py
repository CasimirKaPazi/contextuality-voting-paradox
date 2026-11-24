"""Note "A tight form without a rational diagonal", Section 6: approval with a veto.
Two players each approve a set of proposals (the empty set is a veto). If the approved sets meet,
the outcome is a lottery over the intersection; if not, the fallback F.

1. Two proposals a, b, with outcomes compared by strict orders: ties broken towards a, towards F,
   or by a coin. With the coin, once with all orders and once with the orders an expected utility
   allows (the coin strictly between a and b). Counts the (P, Q) under which each player works.
2. k = 2, 3, 4 proposals with random generic expected utilities: ties by a lottery with fixed
   positive weights, or broken deterministically. Counts players with a rational diagonal, and cases
   where sincere approval (approve exactly what is better than F) is not a strict Nash strategy.
Usage: python3 approval_veto.py"""
import itertools, random

def subsets(props):
    return [frozenset(s) for n in range(len(props) + 1) for s in itertools.combinations(props, n)]

# ---- 1. strict orders on outcomes -------------------------------------------------------------
def works(R, P, Q):
    """Player with rows R and order P has no strict Nash strategy against an opponent with order Q."""
    C = [list(c) for c in zip(*R)]
    for r in R:
        y = min(r, key=Q.index)
        if not any(r[j] == y and any(P.index(v) < P.index(y) for v in C[j]) for j in range(len(r))):
            return False
    return True

def ordinal(tie, outs, allowed):
    S = subsets("ab")
    R = [[("F" if not a & b else next(iter(a & b)) if len(a & b) == 1 else tie) for b in S] for a in S]
    orders = [P for P in itertools.permutations(outs) if allowed(P)]
    T = [list(c) for c in zip(*R)]
    return [sum(works(M, P, Q) for P in orders for Q in orders) for M in (R, T)]

between = lambda P: min(P.index("a"), P.index("b")) < P.index("coin") < max(P.index("a"), P.index("b"))
print("two proposals, strict orders; number of (P, Q) under which player 1 / player 2 works:")
print("  ties to a:                 ", ordinal("a", "abF", lambda P: True))
print("  ties to F:                 ", ordinal("F", "abF", lambda P: True))
print("  ties by a coin, all orders:", ordinal("coin", ["a", "b", "F", "coin"], lambda P: True))
print("  ties by a coin, EU orders: ", ordinal("coin", ["a", "b", "F", "coin"], between))

# ---- 2. expected utilities ------------------------------------------------------------------------
def eu_run(k, trials, lottery, seed=1):
    rng = random.Random(seed)
    S = subsets(range(k)); n = len(S)
    w = [rng.uniform(.5, 2) for _ in range(k)]
    diag = sincere_fail = 0
    for _ in range(trials):
        U = [[rng.random() for _ in range(k)] for _ in range(2)]
        F = [rng.random(), rng.random()]
        def val(p, I):
            if not I: return F[p]
            if lottery: return sum(w[x] * U[p][x] for x in I) / sum(w[x] for x in I)
            return U[p][min(I)]
        V = [[[val(p, S[a] & S[b]) for b in range(n)] for a in range(n)] for p in range(2)]  # V[p][row][col]
        for p in range(2):
            mine = (lambda a, b: V[0][a][b]) if p == 0 else (lambda a, b: V[1][b][a])   # p plays a, opponent b
            theirs = (lambda a, b: V[1][a][b]) if p == 0 else (lambda a, b: V[0][b][a])
            strict = []
            for a in range(n):
                m = max(theirs(a, b) for b in range(n))
                replies = [b for b in range(n) if theirs(a, b) > m - 1e-12]
                if all(mine(a, b) >= max(mine(x, b) for x in range(n)) - 1e-12 for b in replies):
                    strict.append(a)
            diag += not strict
            sincere = S.index(frozenset(x for x in range(k) if U[p][x] > F[p]))
            sincere_fail += sincere not in strict
    return diag, sincere_fail

print("random expected utilities (two players per trial):")
for k, trials in ((2, 3000), (3, 3000), (4, 800)):
    for lottery in (True, False):
        d, s = eu_run(k, trials, lottery)
        print(f"  k={k}, ties by {'a lottery' if lottery else 'the lowest index'}: {2 * trials} players, "
              f"{d} with a rational diagonal, sincere approval not strict Nash for {s}")
