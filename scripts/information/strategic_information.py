"""Plurality against approval under one common rationale: the best reply to a shared poll.

The poll names a leader a1 and a runner-up a2. Pivot events are ordered lexicographically: the tie
between a1 and a2 dominates, then ties between a1 and any other candidate, then ties involving a2,
then all others. This full order is one instance of the note's assumption (T), which is all the proofs
use. A ballot's value is the sum over pivot
pairs {x, y} of (s(x) - s(y)) (u_x - u_y), compared level by level. Checked on random profiles with
strict (continuous) utilities, for impartial culture and a two-dimensional spatial model:

1. Best replies, by brute force over all ballots. Plurality: the preferred of a1 and a2. Approval:
   every candidate above a1, and a1 exactly when a1 is above a2 (the leader rule).
2. Counting (Proposition 1). Given the poll, a1 and a2 have the same tally under both methods,
   every plurality ballot lies inside the same voter's approval ballot, the plurality ballot is a
   function of the approval ballot, and every other candidate x gets N(x > a1) approvals. Leader-rule
   ballots approve the favourite and never the least preferred candidate (admissibility).
3. Self-confirming polls (Proposition 2): polls whose tally ranks a1 first and a2 second, strictly.
   Plurality: every pair in which a1 beats a2 by majority. Approval: exactly the pairs in which a1
   is a Condorcet winner and a2 its strongest challenger. The approval polls are among the
   plurality polls.
4. The majority switch (Proposition 3), with the poll replaced each round by the two highest tallies
   of the round before: a change of leader always goes to a candidate who beats the old leader by
   majority, and a leader beaten by majority never leads two rounds in a row. Reported, no claim:
   from every starting pair, how often the walk ends at the Condorcet winner or cycles; from the
   sincere plurality count, how often the leader after two and after twenty rounds beats the
   plurality winner, among the profiles where that winner is beaten.
6. The profile of the note with a Condorcet winner outside the walk: 102 voters, the cycle a > b > d
   in groups of 35, 34, 33, c second for all but four voters of each group and last for those four.
   c is the Condorcet winner with no first preferences; from the plurality count the leader cycles
   through a, d, b with every tally strict, and c never leads.
7. The walk with memory (Proposition 4): a candidate who has led once is no longer eligible, and
   leader and runner-up are the top two eligible tallies. From the plurality count and from six
   further starting polls, on random profiles with three to eight candidates (walks with ties
   among eligible tallies skipped): the walk ends in the Smith set and its last change of leader
   comes by round 2(m - 1); on the profile of item 6 it reaches the Condorcet winner.
5. Targets (no claim, reported): on profiles with a Condorcet winner, how often the best winner of a
   self-confirming plurality poll has a higher sum of utilities than the Condorcet winner, and how
   often the worst one is not the Condorcet winner.

Ties in tallies are broken by candidate index; profiles where a tie decides a check are counted
separately and skipped. Run: python3 strategic_information.py   (needs numpy; about two minutes)
"""
import itertools
import numpy as np

rng = np.random.default_rng(11)


def profile(n, m, model):
    if model == "impartial":
        return rng.random((n, m))
    voters, cands = rng.normal(size=(n, 2)), rng.normal(size=(m, 2))
    return -np.linalg.norm(voters[:, None, :] - cands[None, :, :], axis=2)


def levels(a1, a2, m):
    """Pivot pairs grouped by order of likelihood, most likely first."""
    others = [x for x in range(m) if x not in (a1, a2)]
    rest = [p for p in itertools.combinations(others, 2)]
    return [[(a1, a2)], [(a1, x) for x in others], [(a2, x) for x in others], rest]


def value(s, u, lev):
    return tuple(sum((s[x] - s[y]) * (u[x] - u[y]) for x, y in L) for L in lev)


def best(ballots, u, lev):
    vals = [value(s, u, lev) for s in ballots]
    top = max(vals)
    winners = [s for s, v in zip(ballots, vals) if v == top]
    return winners[0], len(winners) == 1


def ballots(m):
    plur = [tuple(int(i == c) for i in range(m)) for c in range(m)]
    appr = list(itertools.product((0, 1), repeat=m))
    return plur, appr


def leader_rule(u, a1, a2):
    s = [int(u[x] > u[a1]) for x in range(len(u))]
    s[a1] = int(u[a1] > u[a2])
    return tuple(s)


def tally(B):
    return np.sum(np.array(B), axis=0)


def ranked_top_two(t):
    order = sorted(range(len(t)), key=lambda c: (-t[c], c))
    strict = t[order[0]] > t[order[1]] > (t[order[2]] if len(t) > 2 else -1)
    return order[0], order[1], strict


def beats(U):
    m = U.shape[1]
    return np.array([[np.sum(U[:, x] > U[:, y]) for y in range(m)] for x in range(m)])


def run(n=101, ms=(3, 4, 5, 6), trials=150, br_trials=40):
    plur_b = {m: ballots(m)[0] for m in ms}
    appr_b = {m: ballots(m)[1] for m in ms}
    for model in ("impartial", "spatial"):
        for m in ms:
            br_ok = count_ok = fp_ok = True
            skipped = 0
            dyn = {"Condorcet winner": 0, "other fixed point": 0, "cycle": 0}
            with_cw = 0
            plur_better = plur_worse = 0
            switch_ok = True
            from_p = {"beaten": 0, "round 2": 0, "round 20": 0}
            for t in range(trials):
                U = profile(n, m, model)
                N = beats(U)
                cw = [x for x in range(m) if all(N[x, y] > N[y, x] for y in range(m) if y != x)]
                polls = list(itertools.permutations(range(m), 2))
                if t < br_trials:                                        # 1. best replies
                    a1, a2 = polls[rng.integers(len(polls))]
                    lev = levels(a1, a2, m)
                    for u in U[:10]:
                        bp, _ = best(plur_b[m], u, lev)
                        ba, uniq = best(appr_b[m], u, lev)
                        want_p = a1 if u[a1] > u[a2] else a2
                        br_ok &= bp.index(1) == want_p
                        br_ok &= uniq and ba == leader_rule(u, a1, a2)
                fps = {"plurality": set(), "approval": set()}
                for a1, a2 in polls:                                     # 2. and 3.
                    P = [tuple(int(c == (a1 if u[a1] > u[a2] else a2)) for c in range(m)) for u in U]
                    A = [leader_rule(u, a1, a2) for u in U]
                    tp, ta = tally(P), tally(A)
                    count_ok &= tp[a1] == ta[a1] == N[a1, a2] and tp[a2] == ta[a2] == N[a2, a1]
                    count_ok &= all(p[c] <= a[c] for p, a in zip(P, A) for c in range(m))
                    count_ok &= all(p == tuple(int(c == (a1 if a[a1] else a2)) for c in range(m))
                                    for p, a in zip(P, A))
                    count_ok &= all(ta[x] == N[x, a1] for x in range(m) if x not in (a1, a2))
                    count_ok &= all(a[int(np.argmax(u))] == 1 and a[int(np.argmin(u))] == 0
                                    for a, u in zip(A, U))
                    for name, tl in (("plurality", tp), ("approval", ta)):
                        f, s, strict = ranked_top_two(tl)
                        if (f, s) == (a1, a2) and strict:
                            fps[name].add((a1, a2))
                        elif (f, s) == (a1, a2):
                            skipped += 1
                want_p = {(x, y) for x, y in polls if N[x, y] > N[y, x] and N[y, x] > 0}
                want_a = set()
                for x in cw:
                    ch = [y for y in range(m) if y != x]
                    top = max(N[y, x] for y in ch)
                    if sum(N[y, x] == top for y in ch) == 1:
                        want_a.add((x, max(ch, key=lambda y: N[y, x])))
                fp_ok &= fps["plurality"] == want_p and fps["approval"] == want_a
                fp_ok &= fps["approval"] <= fps["plurality"]
                for start in polls:                                      # 4. majority switch
                    poll, hist = start, [start]
                    for r in range(2 * m + 2):
                        f, s_, _ = ranked_top_two(tally([leader_rule(u, *poll) for u in U]))
                        switch_ok &= f == poll[0] or N[f, poll[0]] > N[poll[0], f]
                        poll = (f, s_)
                        hist.append(poll)
                    for i in range(len(hist) - 2):
                        L = hist[i][0]
                        if any(N[x, L] > N[L, x] for x in range(m) if x != L):
                            switch_ok &= hist[i + 1][0] != L or hist[i + 2][0] != L
                tops = np.bincount(np.argmax(U, axis=1), minlength=m)
                order = sorted(range(m), key=lambda c: (-tops[c], c))
                p, poll, leaders = order[0], (order[0], order[1]), [order[0]]
                for r in range(20):
                    f, s_, _ = ranked_top_two(tally([leader_rule(u, *poll) for u in U]))
                    poll = (f, s_)
                    leaders.append(f)
                if any(N[x, p] > N[p, x] for x in range(m) if x != p):
                    from_p["beaten"] += 1
                    from_p["round 2"] += N[leaders[2], p] > N[p, leaders[2]]
                    from_p["round 20"] += N[leaders[20], p] > N[p, leaders[20]]
                if cw:
                    with_cw += 1
                    welfare = U.sum(axis=0)
                    winners = {x for x, y in fps["plurality"]}
                    plur_better += max(welfare[x] for x in winners) > welfare[cw[0]] + 1e-9
                    plur_worse += min(winners, key=lambda x: welfare[x]) != cw[0]
                    for start in polls:
                        seen, poll = [], start
                        while poll not in seen:
                            seen.append(poll)
                            A = [leader_rule(u, *poll) for u in U]
                            f, s, _ = ranked_top_two(tally(A))
                            poll = (f, s)
                        if seen[-1] == poll:
                            dyn["Condorcet winner" if poll[0] == cw[0] else "other fixed point"] += 1
                        else:
                            dyn["cycle"] += 1
            total = sum(dyn.values())
            print(f"{model:9s} m={m}  best replies {'ok' if br_ok else 'FAIL'}  "
                  f"counting {'ok' if count_ok else 'FAIL'}  self-confirming polls "
                  f"{'ok' if fp_ok else 'FAIL'}  majority switch {'ok' if switch_ok else 'FAIL'}  "
                  f"(ties skipped: {skipped})")
            print(f"{'':9s}      profiles with a Condorcet winner: {with_cw}/{trials}; approval poll "
                  f"dynamics from every start: " +
                  ", ".join(f"{k} {v / total:.3f}" for k, v in dyn.items()))
            print(f"{'':9s}      plurality's best self-confirming winner above the Condorcet winner in "
                  f"total utility: {plur_better}/{with_cw}; its worst one not the Condorcet winner: "
                  f"{plur_worse}/{with_cw}")
            print(f"{'':9s}      from the plurality count, leader beats a beaten plurality winner after "
                  f"2 rounds: {from_p['round 2']}/{from_p['beaten']}, after 20: "
                  f"{from_p['round 20']}/{from_p['beaten']}")


def smith_counterexample():
    a, b, c, d = 0, 1, 2, 3
    def u_of(r):
        u = np.zeros(4)
        for k, x in enumerate(r):
            u[x] = 4 - k
        return u
    U = []
    for (x, y, z), k in (((a, b, d), 35), ((b, d, a), 34), ((d, a, b), 33)):
        U += [u_of((x, c, y, z))] * (k - 4) + [u_of((x, y, z, c))] * 4
    U = np.array(U)
    N = beats(U)
    ok = all(N[c, y] > N[y, c] for y in (a, b, d)) and np.sum(np.argmax(U, axis=1) == c) == 0
    tops = np.bincount(np.argmax(U, axis=1), minlength=4)
    order = sorted(range(4), key=lambda q: (-tops[q], q))
    poll, leaders = (order[0], order[1]), []
    for r in range(30):
        f, s, strict = ranked_top_two(tally([leader_rule(u, *poll) for u in U]))
        ok &= strict
        poll = (f, s)
        leaders.append(f)
    ok &= c not in leaders and leaders[-3:] in ([a, d, b], [d, b, a], [b, a, d])
    mem, _ = memory_walk(N, (order[0], order[1]), 8)
    ok &= mem[-1] == c
    print(f"Condorcet winner outside the walk (note, Section 4a): {'ok' if ok else 'FAIL'}; "
          f"leaders {leaders[:7]}")


def smith_set(N):
    m = len(N)
    order = sorted(range(m), key=lambda x: -sum(N[x, y] > N[y, x] for y in range(m)))
    for k in range(1, m + 1):
        S = set(order[:k])
        if all(N[x, y] > N[y, x] for x in S for y in range(m) if y not in S):
            return S


def memory_walk(N, start, rounds):
    """Leaders of the walk with memory, computed from the pairwise counts (Proposition 1 gives the
    leader-rule tallies: N[L, R] for the leader, N[x, L] for every other candidate)."""
    m = len(N)
    (L, R), led, leaders, tied = start, {start[0]}, [start[0]], False
    for r in range(rounds):
        t = [N[L, R] if x == L else N[x, L] for x in range(m)]
        E = sorted((x for x in range(m) if x not in led or x == L), key=lambda x: (-t[x], x))
        tied |= len(E) > 1 and t[E[0]] == t[E[1]]
        if E[0] != L:
            L = E[0]
            led.add(L)
        rest = sorted((x for x in range(m) if x not in led), key=lambda x: (-t[x], x))
        if not rest:
            leaders += [L] * (rounds - r)
            break
        tied |= len(rest) > 1 and t[rest[0]] == t[rest[1]]
        R = rest[0]
        leaders.append(L)
    return leaders, tied


def check_memory_walk(trials=200):
    ok, walks, skipped = True, 0, 0
    for model in ("impartial", "spatial"):
        for m in range(3, 9):
            for t in range(trials):
                U = profile(101, m, model)
                N = beats(U)
                S = smith_set(N)
                tops = np.bincount(np.argmax(U, axis=1), minlength=m)
                order = sorted(range(m), key=lambda q: (-tops[q], q))
                starts = [(order[0], order[1])] + list(itertools.permutations(range(m), 2))[:6]
                for start in starts:
                    leaders, tied = memory_walk(N, start, 4 * m)
                    if tied:
                        skipped += 1
                        continue
                    walks += 1
                    last = max([i for i in range(1, len(leaders)) if leaders[i] != leaders[i - 1]],
                               default=0)
                    ok &= leaders[-1] in S and last <= 2 * (m - 1)
    print(f"walk with memory: {'ok' if ok else 'FAIL'} on {walks} walks ({skipped} skipped for ties)")


if __name__ == "__main__":
    run()
    smith_counterexample()
    check_memory_walk()
