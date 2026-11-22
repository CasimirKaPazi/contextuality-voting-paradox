"""Three outcomes: predicate abstraction.  For a player i (opponent o) and outcomes:
  F(u)        i forces u;
  Esc(w)      every row containing w has a w-cell in a column with another outcome;
  Rch(m,t)    every row inside {t, m} containing m has an m-cell in a column containing t;
  RchA(m,t)   every row containing m has an m-cell in a column containing t;
  EscT(w,t)   every row inside {t, w} containing w has a w-cell in a column with another outcome.
Then rev(t,m,w) = not F(t) and Esc(w) and Rch(m,t);  rot(t,m,w) = not F(t) and RchA(m,t) and EscT(w,t).
Checks these formulas against the matrix test on stopping games."""
import pickle, itertools, random
from sg import matrix, works_direct
def T(R): return [list(c) for c in zip(*R)]
def feats(R):
    C = T(R); f = {}
    def esc_row(r, u): return any(r[c] == u and any(v != u for v in C[c]) for c in range(len(C)))
    def rch_row(r, u, v): return any(r[c] == u and v in C[c] for c in range(len(C)))
    for u in range(3):
        f["F", u] = any(all(v == u for v in r) for r in R)
        f["Esc", u] = all(esc_row(r, u) for r in R if u in r)
    for m, t in itertools.permutations(range(3), 2):
        f["Rch", m, t] = all(rch_row(r, m, t) for r in R if m in r and set(r) <= {t, m})
        f["RchA", m, t] = all(rch_row(r, m, t) for r in R if m in r)
        f["EscT", m, t] = all(esc_row(r, m) for r in R if m in r and set(r) <= {t, m})
    return f
def rev(f, t, m, w): return not f["F", t] and f["Esc", w] and f["Rch", m, t]
def rot(f, t, m, w): return not f["F", t] and f["RchA", m, t] and f["EscT", w, t]
if __name__ == "__main__":
    data = pickle.load(open("data_k3_N7.pkl", "rb")); random.seed(3)
    bad = 0; n = 0
    for p, o, z, W in random.sample(data, 20000):
        if len(set(o) | {z}) != 3: continue
        for i in (0, 1):
            f = feats(matrix(p, o, z, i))
            for P in itertools.permutations(range(3)):
                n += 2
                bad += rev(f, *P) != works_direct(p, o, z, i, P, P[::-1])
                bad += rot(f, *P) != works_direct(p, o, z, i, P, P[1:] + P[:1])
    print(n, "checks,", bad, "mismatches")
