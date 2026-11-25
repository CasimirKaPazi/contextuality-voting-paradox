"""The walks of *Strategic Information* when ballot mistakes only lose marks (Section 4e).

Voters respond to the previous tally as poll. The front-runners are decided as under the leader rule;
a candidate x ranked third or lower is approved when it is preferred to the lottery over the candidates
ranked above it with weights (s_y - s_x)^2, the limiting ratios of its ties in Laslier's model with lost
marks (see ballot_mistakes.py). This is compared with the leader rule, on random profiles of 101 voters
(impartial culture and a two-dimensional spatial model) with three to five candidates, starting from
the plurality count. Reported, no claim:
- the walk of Section 4a (poll = previous tally): how often a new leader does not beat the old one by
  majority, how often the walk reaches the Condorcet winner, settles elsewhere, cycles, and ends in
  the Smith set;
- the walk with memory of Section 4b: how often it ends in the Smith set.
Run: python3 lost_marks_walk.py   (needs numpy; a few seconds)
"""
import itertools
import numpy as np

rng = np.random.default_rng(12)


def profile(n, m, model):
    if model == "impartial":
        return rng.random((n, m))
    v, c = rng.normal(size=(n, 2)), rng.normal(size=(m, 2))
    return -np.linalg.norm(v[:, None] - c[None], axis=2)


def ballots(U, s, rule):
    """Best ballots against the poll s (candidates ranked by s, ties by index)."""
    n, m = U.shape
    order = sorted(range(m), key=lambda x: (-s[x], x))
    a1, a2 = order[0], order[1]
    B = np.zeros((n, m), int)
    B[:, a1] = U[:, a1] > U[:, a2]
    B[:, a2] = U[:, a2] > U[:, a1]
    for k in range(2, m):
        x, above = order[k], order[:k]
        if rule == "leader":
            thr = U[:, a1]
        else:
            w = np.array([(s[y] - s[x]) ** 2 for y in above]) + 1e-12
            thr = U[:, above] @ w / w.sum()
        B[:, x] = U[:, x] > thr
    return B, a1


def pairwise(U):
    m = U.shape[1]
    return np.array([[np.sum(U[:, x] > U[:, y]) for y in range(m)] for x in range(m)])


def smith(N):
    m = len(N)
    for k in range(1, m + 1):
        for S in itertools.combinations(range(m), k):
            if all(N[x, y] > N[y, x] for x in S for y in range(m) if y not in S):
                return set(S)


def plain_walk(U, N, rule):
    m = U.shape[1]
    s = np.bincount(np.argmax(U, axis=1), minlength=m).astype(float)
    seen, changes, bad = [], 0, 0
    while True:
        key = tuple(sorted(range(m), key=lambda x: (-s[x], x)))
        if key in seen:
            break
        seen.append(key)
        B, a1 = ballots(U, s, rule)
        s = B.sum(axis=0).astype(float)
        new = sorted(range(m), key=lambda x: (-s[x], x))[0]
        if new != a1:
            changes += 1
            bad += not N[new, a1] > N[a1, new]
    loop = seen[seen.index(key):]
    return [k[0] for k in loop], len(loop) == 1, changes, bad


def memory_walk(U, N, rule):
    m = U.shape[1]
    s = np.bincount(np.argmax(U, axis=1), minlength=m).astype(float)
    order = sorted(range(m), key=lambda x: (-s[x], x))
    L, R, led = order[0], order[1], {order[0]}
    for r in range(4 * m):
        poll = s.copy()
        poll[L], poll[R] = s.max() + 2, s.max() + 1      # the published leader and runner-up first
        B, _ = ballots(U, poll, rule)
        tal = B.sum(axis=0)
        E = [x for x in range(m) if x not in led or x == L]
        new = sorted(E, key=lambda x: (-tal[x], x))[0]
        led.add(new)
        L = new
        rest = [x for x in range(m) if x != L and x not in led]
        if not rest:
            break
        R = sorted(rest, key=lambda x: (-tal[x], x))[0]
        s = tal.astype(float)
    return L


def main(trials=400):
    for model in ("impartial", "spatial"):
        for m in (3, 4, 5):
            line = []
            for rule in ("leader", "lost"):
                cw_n = cw_hit = wrong = cyc = sm = ch = bad = mem = 0
                for t in range(trials):
                    U = profile(101, m, model)
                    N = pairwise(U)
                    S = smith(N)
                    cw = [x for x in range(m) if all(N[x, y] > N[y, x] for y in range(m) if y != x)]
                    loop, fixed, c, b = plain_walk(U, N, rule)
                    ch, bad = ch + c, bad + b
                    cyc += not fixed
                    sm += set(loop) <= S
                    if cw:
                        cw_n += 1
                        cw_hit += fixed and loop[0] == cw[0]
                        wrong += fixed and loop[0] != cw[0]
                    mem += memory_walk(U, N, rule) in S
                line.append(f"{rule}: changes not beating the old leader {bad}/{ch}, Condorcet winner "
                            f"reached {cw_hit}/{cw_n}, settled elsewhere {wrong}, cycles {cyc}, "
                            f"ends in the Smith set {sm}; with memory in the Smith set {mem}/{trials}")
            print(f"{model} m={m}\n  " + "\n  ".join(line))


if __name__ == "__main__":
    main()
