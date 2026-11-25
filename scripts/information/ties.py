"""Ties in the walk of *Strategic Information*, Section 4d. Ballots are strict rankings drawn from
impartial culture or a two-dimensional spatial model, with odd and even numbers of voters, so that
pairwise counts can tie. Tallies are the leader-rule tallies (N(L > R) for the leader, N(x > L) for
every other candidate), and ties among the eligible tallies are broken by a fixed order or at random.

Checked for the walk with memory: with no pairwise ties (odd electorates) every change of leader goes
to a candidate that beats the old leader, whatever the tie-break; with pairwise ties every change goes
to a candidate that beats or ties it; in both cases the final leader is in the Smith set (members beat
every non-member), and the last change comes by round 2(m - 1) with any tie-break in odd electorates and with the fixed
tie-break in even ones. With random tie-breaks in even electorates the bound can be exceeded, and the final leader beats or ties every
candidate that never led. Reported: how often a change goes along a tie.
The Schwartz set (union of the smallest sets no outsider beats), on profiles where it differs from the
Smith set: reported how often the walk with memory ends in it with each tie-break; and, when a tie for
the lead never dethrones the current leader (every change then a strict defeat), checked that the walk
without memory never leaves the Schwartz set once its leader is in it, reported how often each walk ends
there.
Run: python3 ties.py   (needs numpy; a few seconds)
"""
import itertools
import random
import numpy as np

rng = np.random.default_rng(4)
random.seed(4)


def profile(n, m, model):
    if model == "impartial":
        return [tuple(rng.permutation(m)) for _ in range(n)]
    v, c = rng.normal(size=(n, 2)), rng.normal(size=(m, 2))
    return [tuple(np.argsort(r)) for r in np.linalg.norm(v[:, None] - c[None], axis=2)]


def counts(P, m):
    N = np.zeros((m, m), int)
    for r in P:
        pos = {x: k for k, x in enumerate(r)}
        for x in range(m):
            for y in range(m):
                N[x, y] += pos[x] < pos[y]
    return N


def smith(N, m):
    for k in range(1, m + 1):
        for S in itertools.combinations(range(m), k):
            if all(N[x, y] > N[y, x] for x in S for y in range(m) if y not in S):
                return set(S)


def pick(cands, t, rule):
    top = max(t[x] for x in cands)
    best = [x for x in cands if t[x] == top]
    return min(best) if rule == "fixed" else random.choice(best)


def memory_walk(N, m, start, rule, rounds):
    (L, R), led, changes = start, {start[0]}, []
    for r in range(rounds):
        t = [N[L, R] if x == L else N[x, L] for x in range(m)]
        new = pick([x for x in range(m) if x not in led or x == L], t, rule)
        if new != L:
            changes.append((r + 1, N[new, L] > N[L, new], N[new, L] == N[L, new]))
            led.add(new)
        L = new
        rest = [x for x in range(m) if x != L and x not in led]
        if not rest:
            break
        R = pick(rest, t, rule)
    return L, led, changes


def main(trials=1500):
    for parity, sizes in (("odd", (5, 7, 9, 11, 21)), ("even", (4, 6, 8, 10, 20))):
        for rule in ("fixed", "random"):
            strict = weak = in_smith = bound = beats_never = True
            moves = tie_moves = 0
            for t in range(trials):
                n, m = random.choice(sizes), random.choice((3, 4, 5))
                N = counts(profile(n, m, random.choice(("impartial", "spatial"))), m)
                L, led, ch = memory_walk(N, m, tuple(random.sample(range(m), 2)), rule, 60)
                moves += len(ch)
                tie_moves += sum(c[2] for c in ch)
                if parity == "odd":
                    strict &= all(c[1] for c in ch)
                weak &= all(c[1] or c[2] for c in ch)
                in_smith &= L in smith(N, m)
                if rule == "fixed" or parity == "odd":
                    bound &= max([c[0] for c in ch], default=0) <= 2 * (m - 1)
                beats_never &= all(N[L, x] >= N[x, L] for x in range(m) if x not in led)
            print(f"{parity:4s} electorates, {rule:6s} tie-break: "
                  f"{'every change a strict defeat' if parity == 'odd' else 'every change a defeat or tie'}: "
                  f"{'ok' if (strict if parity == 'odd' else weak) else 'FAIL'}; ends in the Smith set: "
                  f"{'ok' if in_smith else 'FAIL'}; "
                  + (f"bound 2(m - 1): {'ok' if bound else 'FAIL'}; " if rule == "fixed" or parity == "odd" else "")
                  + f"final leader beats or ties every candidate never led: {'ok' if beats_never else 'FAIL'}; "
                  f"changes along ties: {tie_moves}/{moves}")


def schwartz(N, m):
    R = [[N[x, y] > N[y, x] or x == y for y in range(m)] for x in range(m)]
    for k in range(m):
        for i in range(m):
            for j in range(m):
                R[i][j] = R[i][j] or (R[i][k] and R[k][j])
    return {x for x in range(m) if all(R[x][y] for y in range(m) if R[y][x])}


def incumbent_walk(N, m, start, memory, rounds=120):
    (L, R), led, leaders = start, {start[0]}, [start[0]]
    for r in range(rounds):
        t = [N[L, R] if x == L else N[x, L] for x in range(m)]
        E = [x for x in range(m) if not memory or x not in led or x == L]
        top = max(t[x] for x in E)
        L = L if t[L] == top else random.choice([x for x in E if t[x] == top])
        led.add(L)
        leaders.append(L)
        rest = [x for x in range(m) if x != L and (not memory or x not in led)]
        if not rest:
            break
        R = random.choice([x for x in rest if t[x] == max(t[y] for y in rest)])
    return leaders


def schwartz_checks(trials=4000):
    for rule in ("fixed", "random"):
        differ = inside = 0
        for t in range(trials):
            n, m = random.choice((4, 6, 8, 10)), random.choice((3, 4, 5, 6))
            N = counts(profile(n, m, random.choice(("impartial", "spatial"))), m)
            Sw = schwartz(N, m)
            if smith(N, m) == Sw:
                continue
            differ += 1
            L, led, ch = memory_walk(N, m, tuple(random.sample(range(m), 2)), rule, 60)
            inside += L in Sw
        print(f"Schwartz set, walk with memory, {rule} tie-break: ends in it {inside}/{differ}")
    for memory in (False, True):
        differ = inside = 0
        never_left = True
        for t in range(trials):
            n, m = random.choice((4, 6, 8, 10)), random.choice((3, 4, 5, 6))
            N = counts(profile(n, m, random.choice(("impartial", "spatial"))), m)
            Sw = schwartz(N, m)
            if smith(N, m) == Sw:
                continue
            differ += 1
            leaders = incumbent_walk(N, m, tuple(random.sample(range(m), 2)), memory)
            k = next((i for i, x in enumerate(leaders) if x in Sw), None)
            if k is not None:
                never_left &= all(x in Sw for x in leaders[k:])
            inside += (set(leaders[-30:]) <= Sw) if not memory else leaders[-1] in Sw
        print(f"incumbent keeps tied leads, {'with' if memory else 'without'} memory: never leaves the "
              f"Schwartz set: {'ok' if never_left else 'FAIL'}; ends in it {inside}/{differ}")


if __name__ == "__main__":
    main()
    schwartz_checks()
