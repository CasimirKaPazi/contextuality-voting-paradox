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

# ---- 3. several players -------------------------------------------------------------------------
def n_run(n, k, trials, lottery, seed=2):
    rng = random.Random(seed)
    S = subsets(range(k)); m = len(S)
    w = [rng.uniform(.5, 2) for _ in range(k)]
    diag = sincere_fail = 0
    for _ in range(trials):
        U = [[rng.random() for _ in range(k)] for _ in range(n)]; F = [rng.random() for _ in range(n)]
        def val(p, prof):
            I = frozenset(range(k))
            for s in prof: I &= S[s]
            if not I: return F[p]
            return sum(w[x] * U[p][x] for x in I) / sum(w[x] for x in I) if lottery else U[p][min(I)]
        for i in range(n):
            others = [p for p in range(n) if p != i]
            def full(b, c): prof = list(c); prof.insert(i, b); return prof
            strict = []
            for b in range(m):
                ok = True
                for c in itertools.product(range(m), repeat=n - 1):
                    eq = all(val(p, full(b, c)) >= max(val(p, full(b, c[:t] + (d,) + c[t + 1:])) for d in range(m)) - 1e-12
                             for t, p in enumerate(others))
                    if eq and val(i, full(b, c)) < max(val(i, full(x, c)) for x in range(m)) - 1e-12: ok = False; break
                if ok: strict.append(b)
            diag += not strict
            sincere_fail += S.index(frozenset(x for x in range(k) if U[i][x] > F[i])) not in strict
    return diag, sincere_fail

print("several players:")
for n, k, trials in ((3, 2, 300), (3, 3, 60), (4, 2, 60)):
    for lottery in (True, False):
        d, s = n_run(n, k, trials, lottery)
        print(f"  {n} players, k={k}, ties by {'a lottery' if lottery else 'the lowest index'}: {n * trials} players, "
              f"{d} with a rational diagonal, sincere approval not strict Nash for {s}")

# ---- 4. random ballot over declared ideals as the fallback --------------------------------------
def rb_run(k, trials, seed=3):
    rng = random.Random(seed)
    S = subsets(range(k)); strat = [(a, d) for a in S for d in range(k)]; n = len(strat)
    diag = 0
    for _ in range(trials):
        U = [[rng.random() for _ in range(k)] for _ in range(2)]
        def val(p, s, t):          # s is player 0's strategy, t player 1's
            I = s[0] & t[0]
            return sum(U[p][x] for x in I) / len(I) if I else (U[p][s[1]] + U[p][t[1]]) / 2
        for p in range(2):
            def mine(a, b): return val(p, *((strat[a], strat[b]) if p == 0 else (strat[b], strat[a])))
            def theirs(a, b): return val(1 - p, *((strat[a], strat[b]) if p == 0 else (strat[b], strat[a])))
            strict = [a for a in range(n)
                      if all(mine(a, b) >= max(mine(x, b) for x in range(n)) - 1e-12
                             for b in range(n) if theirs(a, b) >= max(theirs(a, c) for c in range(n)) - 1e-12)]
            diag += not strict
    return diag

print("random ballot over declared ideals as the fallback, ties by a uniform lottery:")
for k in (2, 3):
    print(f"  k={k}: 2000 players, {rb_run(k, 1000)} with a rational diagonal")
