"""Larger groups: the comparisons of Sections 3d and 3i for six to eight participants.

The earlier computations enumerate every group for three to five participants. Here the same
process is computed for six, seven and eight participants (with n + 2 outcomes), with a single
proposer at every group (the Raiffa one-step rule of Section 3d, which is the call game of Section 3g),
for the four kinds of exclusion of Section 3i, and with one stubborn participant who vetoes every
proposal they may veto. The family of points on a line with linear loss is left out: there every
variant gives the value of the mean of the ideals (Section 3d).

Reported per family and size, in units of each participant's utility range: mean gain over the
endowment, share of participants below it, largest shortfall; with a stubborn participant, the
others' mean gain and their share below the endowment.
Run: python3 larger_groups.py   (numpy and scipy; about ten minutes)
"""
import numpy as np

from bargaining_rules import endowments, families
from proposer_groups import holdings, SIZES, TOPS

SIZES_N = ((6, 12), (7, 10), (8, 6))      # (participants, instances)


def main(seed=11):
    rng = np.random.default_rng(seed)
    one = SIZES["one"]
    for fam, gen in families(rng).items():
        if fam.startswith("line, linear"):
            continue
        for n, T in SIZES_N:
            inst = [gen(n, n + 2) for _ in range(T)]
            print(f"{fam}, {n} participants ({T} instances)")
            for top in TOPS:
                g = []
                for U in inst:
                    e = endowments(U); span = U.max(1) - U.min(1)
                    g.extend((holdings(U, one, top) - e) / span)
                g = np.array(g)
                print(f"   {top:10s}: mean gain {g.mean():+.4f}   below endowment {np.mean(g < -1e-7):5.3f}   "
                      f"largest shortfall {max(0.0, -g.min()):.3f}")
            for top in ("sequential", "floor veto"):
                rest = []
                for U in inst:
                    e = endowments(U); span = U.max(1) - U.min(1)
                    rest.extend(((holdings(U, one, top, stubborn=0) - e) / span)[1:])
                rest = np.array(rest)
                print(f"   {top:10s}, one stubborn participant: others' mean gain {rest.mean():+.4f}   "
                      f"others below endowment {np.mean(rest < -1e-7):5.3f}")


if __name__ == "__main__":
    main()
