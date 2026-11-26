"""Instant runoff against plurality with three candidates under a poll-based rationale
(*Instant Runoff and Plurality*, Sections 3 and 4).

A poll for instant runoff names the candidate e expected to be eliminated, the finalists L (expected
winner) and R, the finalist r who is closer to e in first preferences (the other finalist is o), and
W, the winner of the final between o and e that would follow if r were eliminated instead.  Two pivot
events are weighed (labels as in Eggers and Nowacki):

  F  the final between L and R is tied: a ballot counts for whichever of L, R it ranks higher;
  E  r and e are tied for elimination: a first preference for r makes the winner L, a first
     preference for e makes it W, a first preference for o has no effect.

The weight of E relative to F is t: 'F' means F lexicographically first, 'E' means E first, a number
means value = F-effect + t * E-effect.  Remaining ties between ballots are broken towards the sincere
ranking (fewest inverted pairs), standing for the less likely events.

A poll is self-confirming if the strategic ballots reproduce it: e strictly last and r strictly below
o in first preferences, L beating R in the final, and W the winner of o against e (strictly).

Checked, for random profiles (impartial culture with random utilities, and a two-dimensional spatial
model; 101 voters):
  1. with F first, every best reply ranks the preferred of L and R above the other, so the final
     count is N(L > R) against N(R > L) and the strategic plurality count (poll (L, R)) is a
     function of the strategic IRV count; how often this fails when E comes first;
  2. the winners at self-confirming IRV polls are among the winners at self-confirming plurality polls;
  3. how often a self-confirming IRV poll elects a candidate other than the Condorcet winner, and how
     often there is none.
About two minutes.
"""
import itertools, random

C = (0, 1, 2)
RANKINGS = list(itertools.permutations(C))


def inversions(b, rank):
    pos = {c: i for i, c in enumerate(rank)}
    return sum(1 for i in range(3) for j in range(i + 1, 3) if pos[b[i]] > pos[b[j]])


def best_irv(u, poll, t):
    L, R, e, r, W = poll
    sincere = tuple(sorted(C, key=lambda c: -u[c]))

    def dF(b):
        hi, lo = (L, R) if b.index(L) < b.index(R) else (R, L)
        return (u[hi] - u[lo]) / 2

    def dE(b):
        return (u[L] - u[W]) / 2 if b[0] == r else (u[W] - u[L]) / 2 if b[0] == e else 0.0

    if t == 'F':
        key = lambda b: (round(dF(b), 12), round(dE(b), 12), -inversions(b, sincere))
    elif t == 'E':
        key = lambda b: (round(dE(b), 12), round(dF(b), 12), -inversions(b, sincere))
    else:
        key = lambda b: (round(dF(b) + t * dE(b), 12), -inversions(b, sincere))
    return max(RANKINGS, key=key)


def polls():
    for L, R in itertools.permutations(C, 2):
        e = 3 - L - R
        for r in (L, R):
            o = R if r == L else L
            for W in (o, e):
                yield (L, R, e, r, W)


def above(B, x, y):
    a = sum(1 for b in B if b.index(x) < b.index(y))
    return a, len(B) - a


def irv_self_confirming(U, t):
    out = []
    for P in polls():
        L, R, e, r, W = P
        o = R if r == L else L
        B = [best_irv(u, P, t) for u in U]
        first = [sum(1 for b in B if b[0] == c) for c in C]
        if not first[e] < first[r] < first[o]:
            continue
        a, b = above(B, L, R)
        x, y = above(B, o, e)
        if a > b and x != y and (o if x > y else e) == W:
            out.append(P)
    return out


def beats(U, x, y):
    return sum(1 for u in U if u[x] > u[y]) > len(U) / 2


def plurality_self_confirming(U):
    return [(a, b) for a, b in itertools.permutations(C, 2)
            if beats(U, a, b) and any(u[b] > u[a] for u in U)]


def condorcet_winner(U):
    for x in C:
        if all(beats(U, x, y) for y in C if y != x):
            return x


def profile(model, n, rng):
    if model == 'ic':
        return [[rng.random() for _ in C] for _ in range(n)]
    cand = [(rng.gauss(0, 1), rng.gauss(0, 1)) for _ in C]
    out = []
    for _ in range(n):
        v = (rng.gauss(0, 1), rng.gauss(0, 1))
        out.append([-((v[0] - c[0]) ** 2 + (v[1] - c[1]) ** 2) ** .5 for c in cand])
    return out


def main(trials=400, n=101):
    for model in ('ic', 'spatial'):
        for t in ('F', 1, 'E'):
            rng = random.Random(7)
            S = dict(order_kept=0, voters=0, subset=0, with_cw=0, none=0, other=0, no_cw_some=0)
            for _ in range(trials):
                U = profile(model, n, rng)
                for P in polls():                       # 1. the final count is sincere
                    L, R = P[0], P[1]
                    for u in U:
                        b = best_irv(u, P, t)
                        S['voters'] += 1
                        S['order_kept'] += (b.index(L) < b.index(R)) == (u[L] > u[R])
                sc = irv_self_confirming(U, t)
                won = {P[0] for P in sc}
                S['subset'] += won <= {a for a, b in plurality_self_confirming(U)}
                c = condorcet_winner(U)
                if c is None:
                    S['no_cw_some'] += bool(sc)
                else:
                    S['with_cw'] += 1
                    S['none'] += not sc
                    S['other'] += any(w != c for w in won)
            print(f"{model:8s} weight of E: {str(t):2s}  final pair ranked sincerely in "
                  f"{S['order_kept']}/{S['voters']} best replies; IRV winners among plurality's: "
                  f"{S['subset']}/{trials}; with a Condorcet winner ({S['with_cw']} profiles): "
                  f"no self-confirming IRV poll {S['none']}, one electing another candidate "
                  f"{S['other']}; without one, some self-confirming poll: {S['no_cw_some']}")


if __name__ == "__main__":
    main()
