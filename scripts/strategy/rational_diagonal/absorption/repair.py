"""Repair moves.  For a valid game G', a valid front extension (q, x) with x present, and a
working config c of G' that does not absorb (q, x): is there a working config c' of G', obtained
from c by a small move, that absorbs (q, x)?  Moves: swap two outcomes of P (same player and
kind), switch the kind, both, or switch the player (any order)."""
import pickle, collections, sys
from itertools import combinations
from sg import present, valid
from absorb import absorbs

def swaps(P):
    for a, b in combinations(range(len(P)), 2):
        L = list(P); L[a], L[b] = L[b], L[a]; yield tuple(L)

k = int(sys.argv[1]); N = int(sys.argv[2])
data = pickle.load(open(f"data_k{k}_N{N}.pkl", "rb"))
st = collections.Counter()
for p, o, z, W in data:
    g = (p, o, z)
    for q in (0, 1):
        for x in present(o, z):
            if not valid((q,) + p, (x,) + o, z): continue
            for c in W:
                if absorbs(g, c, q, x): continue
                i, P, kind = c; other = "rot" if kind == "rev" else "rev"
                found = None
                for name, cands in (
                    ("swap in P", [(i, P2, kind) for P2 in swaps(P)]),
                    ("switch kind", [(i, P, other)]),
                    ("swap and switch kind", [(i, P2, other) for P2 in swaps(P)]),
                    ("other player", [c2 for c2 in W if c2[0] != i])):
                    if any(c2 in W and absorbs(g, c2, q, x) for c2 in cands):
                        found = name; break
                st[(("own" if i == q else "opponent's"), found)] += 1
for kk in sorted(st, key=str): print(kk, st[kk])
