"""Restrict working configs to a canonical family: for each (i, top x, kind) a single order P
= x followed by the other outcomes sorted by a key computed from the game.  Does
'absorbed iff the extension is valid' still hold, and does every valid game keep a working
config?"""
import pickle, collections, sys
from sg import present, valid, works_direct
from collect import rev, rot
from absorb import absorbs

def positions(p, o, z):
    seq = list(o) + [z]
    first = {}; last = {}
    for t, x in enumerate(seq):
        first.setdefault(x, t); last[x] = t
    return first, last

KEYS = {
    "first appearance": lambda f, l, x: f[x],
    "first appearance, reversed": lambda f, l, x: -f[x],
    "last appearance": lambda f, l, x: l[x],
    "last appearance, reversed": lambda f, l, x: -l[x],
}

def family(g, key):
    p, o, z = g; pr = sorted(present(o, z)); f, l = positions(p, o, z); C = []
    for i in (0, 1):
        for x in pr:
            rest = sorted((y for y in pr if y != x), key=lambda y: KEYS[key](f, l, y))
            P = (x,) + tuple(rest)
            for kind, Q in (("rev", rev(P)), ("rot", rot(P))):
                if works_direct(p, o, z, i, P, Q): C.append((i, P, kind))
    return C

k = int(sys.argv[1]); N = int(sys.argv[2])
data = pickle.load(open(f"data_k{k}_N{N}.pkl", "rb"))
for key in KEYS:
    st = collections.Counter()
    for p, o, z, W in data:
        g = (p, o, z); C = family(g, key)
        st["games without a working canonical config"] += not C
        for q in (0, 1):
            for x in present(o, z):
                if valid((q,) + p, (x,) + o, z):
                    st["valid extensions not absorbed"] += not any(absorbs(g, c, q, x) for c in C)
    print(f"{key:28s}", dict(st))
