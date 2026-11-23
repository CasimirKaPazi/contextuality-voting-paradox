"""Proposals inside the call, with nested proposer groups (CORE note, Section 3i).

The protocol. A call draws a proposer group T uniformly among the groups of a given size, possibly
including the caller. T works out a proposal by the same protocol among its own members: internal
calls draw sub-groups, and an internal veto excludes one member of T, uniformly, from T's work only.
Once T has a proposal, all of T returns to the group. If every member accepts, the proposal is enacted;
if anyone vetoes, one member of the group is drawn uniformly and excluded, and deliberation continues.

Complete information and rational play: accepting exactly what is worth at least the alternative is
weakly dominant at every level, and the proposer of a single-member group proposes their best lottery
among those every member accepts (ties broken towards the others). A group T working for a target
set B (lotteries every member of the higher level accepts) falls back on the average of the proposals
of T minus one member; its own members accept only what beats that fallback; a drawn sub-group then
works for the smaller target.

Sizes of proposer groups: one member; about half (s // 2, at least one); all but one (the mirror of
exclusion). Exclusion at the top level, three variants:
  sequential   the excluded member keeps their stake and loses their voice (CORE's sequential variant)
  one-shot     a veto at the full group goes straight to the random ballot
  veto kept    the excluded member leaves the draw for the last place and the proposer draws, but keeps
               their veto over every later proposal
  floor veto   as veto kept, but an excluded member's veto counts only against proposals worth less to
               them than the random ballot over the members still in the draw (this needs the floor to
               be checkable; otherwise it is an assumption on behaviour, not a rule)
Part 1 reports per family of Section 3d, in units of each participant's utility range: mean gain over the
endowment, the share of participants below it and the largest shortfall.
Part 2: one stubborn participant, who vetoes every proposal they may veto; everyone else plays as in
part 1. Reported: the mean gain of the others, the stubborn participant's mean gain, and the share of
the others below their endowment.
Run: python3 proposer_groups.py 1   or   python3 proposer_groups.py 2   (numpy and scipy; about five
minutes for each part)
"""
import sys
import itertools
import numpy as np

from bargaining_rules import lp_max, endowments, families

TOL = 1e-10
SIZES = {"one": lambda s: 1, "half": lambda s: max(1, s // 2), "all but one": lambda s: s - 1}
TOPS = ["sequential", "one-shot", "veto kept", "floor veto"]


def best(rows, thr, obj, others):
    """Best lottery for obj among those with rows @ x >= thr; ties broken towards others."""
    K = rows.shape[1]
    x, v = lp_max(obj, -rows, -(thr - TOL), K)
    x2, _ = lp_max(others, np.vstack([-rows, -obj[None]]), np.r_[-(thr - TOL), -(v - 1e-9)], K)
    return x if x2 is None else x2


def holdings(U, size, top, stubborn=None):
    n, K = U.shape
    ideal = U.argmax(1)
    H = {frozenset([j]): np.eye(K)[ideal[j]] for j in range(n)}
    for r in range(2, n + 1):
        for S in map(frozenset, itertools.combinations(range(n), r)):
            if top == "one-shot" and r < n:
                continue
            mem = sorted(S)
            if top == "one-shot":
                c = np.bincount(ideal[mem], minlength=K) / r
            else:
                c = sum(H[S - {k}] for k in S) / r            # the value of an exclusion
            out = [i for i in range(n) if i not in S]
            if top == "veto kept":                           # who must accept, and against what
                voters, vthr = U, U @ c
            elif top == "floor veto" and out:
                rb = np.bincount(ideal[mem], minlength=K) / r
                voters, vthr = np.vstack([U[mem], U[out]]), np.r_[U[mem] @ c, U[out] @ rb]
            else:
                voters, vthr = U[mem], U[mem] @ c
            if stubborn is not None and (stubborn in S or top == "veto kept"):
                H[S] = c                                     # every proposal is vetoed
                continue
            others = voters.sum(0)
            memo = {}

            def W(T, chain):
                """The proposal group T arrives at; chain holds the targets added on the way down."""
                key = (T, tuple(G for G, _ in chain))
                if key in memo:
                    return memo[key]
                rows = np.vstack([voters] + [U[sorted(G)] for G, _ in chain])
                thr = np.concatenate([vthr] + [t for _, t in chain])
                if len(T) == 1:
                    m = next(iter(T))
                    x = best(rows, thr, U[m], others - U[m])
                else:
                    fallback = np.mean([W(T - {k}, chain) for k in T], axis=0)   # internal exclusion
                    sub = chain + ((T, U[sorted(T)] @ fallback),)
                    t = min(size(len(T)), len(T) - 1)
                    x = np.mean([W(frozenset(G), sub) for G in itertools.combinations(sorted(T), t)],
                                axis=0)
                memo[key] = x
                return x

            H[S] = np.mean([W(frozenset(T), ()) for T in itertools.combinations(mem, size(r))], axis=0)
    return U @ H[frozenset(range(n))]


def instances(sizes=((3, 5, 30), (4, 6, 20), (5, 7, 6)), seed=3):
    rng = np.random.default_rng(seed)
    for fam, gen in families(rng).items():
        yield fam, [gen(n, K) for n, K, T in sizes for _ in range(T)]


def part1():
    for fam, inst in instances():
        print(f"Part 1, {fam} ({len(inst)} instances)")
        for top in TOPS:
            for name, size in SIZES.items():
                g = []
                for U in inst:
                    e = endowments(U); span = U.max(1) - U.min(1)
                    g.extend((holdings(U, size, top) - e) / span)
                g = np.array(g)
                print(f"   {top:10s} proposer groups {name:11s}: mean gain {g.mean():+.4f}   below endowment "
                      f"{np.mean(g < -1e-7):5.3f}   largest shortfall {max(0.0, -g.min()):.3f}")


def part2():
    for fam, inst in instances():
        print(f"Part 2, {fam}: participant 0 vetoes everything")
        for top in TOPS:
            for name in ("one", "all but one"):
                rest, stub = [], []
                for U in inst:
                    e = endowments(U); span = U.max(1) - U.min(1)
                    g = (holdings(U, SIZES[name], top, stubborn=0) - e) / span
                    rest.extend(g[1:]); stub.append(g[0])
                rest = np.array(rest)
                print(f"   {top:10s} proposer groups {name:11s}: others' mean gain {rest.mean():+.4f}   "
                      f"stubborn member's {np.mean(stub):+.4f}   others below endowment {np.mean(rest < -1e-7):5.3f}")


if __name__ == "__main__":
    {"1": part1, "2": part2}[sys.argv[1] if len(sys.argv) > 1 else "1"]()
