"""The stack of degrees of a strategy-proof lottery for one voter (working note *The Global Form*,
Section 8). Three and four alternatives.

The deterministic strategy-proof rules for one voter are the rules "best of S" (the voter's best
alternative in a fixed non-empty set S). Every SD-strategy-proof lottery is an affine combination of
them, with unique coefficients c_S, and c_S is the degree of the lottery on the face of the
permutohedron where S occupies the bottom block: the probability of the bottom alternative (|S| = 1),
the flow of the bottom swap (|S| = 2), the winding on the bottom hexagon (|S| = 3), the top degree
(|S| = m). A lottery is a mixture of deterministic rules exactly when every c_S is non-negative.

Part 1: the 2^m - 1 rules "best of S" are affinely independent, and the SD-strategy-proof lotteries
        lie in their affine hull (exact linear programs).
Part 2: smallest coefficient over SD-strategy-proof lotteries, alone and with the windings of
        dimension 2 and the top degree required to be non-negative (exact linear programs).
Part 3: on random vertices of the polytope, c_S equals the degree on every face with S at the bottom.
Part 4: positional rules "k-th choice": top degrees (-1)^(k-1) C(m-1, k-1), counted on the faces of
        the permutohedron. Neutral lotteries with weights w_1 >= ... >= w_m (three to six
        alternatives): a mixture of deterministic rules exactly when all finite differences of w are
        non-negative; the coefficient of "best of S", |S| = j, is the (j-1)-th difference at the bottom
        end (Newton's forward formula).
Run: python3 degree_tower.py   (numpy and scipy; under a minute)
"""
import itertools
from math import comb

import numpy as np
from scipy.optimize import linprog


class OneVoter:
    def __init__(self, m):
        self.m = m
        self.alts = list(range(m))
        self.R = list(itertools.permutations(self.alts))
        self.idx = {r: i for i, r in enumerate(self.R)}
        self.nv = len(self.R) * m
        self.subsets = [S for k in range(1, m + 1) for S in itertools.combinations(self.alts, k)]
        self.V = np.array([self.best_of(S) for S in self.subsets])
        self._sdsp()
        self.faces = self._hexagons()

    def var(self, r, a):
        return self.idx[r] * self.m + a

    def rule(self, f):
        v = np.zeros(self.nv)
        for r in self.R:
            out = f(r)
            if isinstance(out, dict):
                for a, q in out.items():
                    v[self.var(r, a)] += q
            else:
                v[self.var(r, out)] = 1
        return v

    def best_of(self, S):
        return self.rule(lambda r: next(a for a in r if a in S))

    def _sdsp(self):
        A, b, E, e = [], [], [], []
        for r in self.R:
            row = np.zeros(self.nv); row[[self.var(r, a) for a in self.alts]] = 1
            E.append(row); e.append(1.0)
            for rp in self.R:
                if rp == r:
                    continue
                for k in range(1, self.m):
                    row = np.zeros(self.nv)
                    for a in r[:k]:
                        row[self.var(rp, a)] += 1; row[self.var(r, a)] -= 1
                    A.append(row); b.append(0.0)
        self.A, self.b, self.E, self.e = map(np.array, (A, b, E, e))

    # ---- faces of dimension 2: three consecutive positions permuted, the others fixed
    def _hexagons(self):
        m, out = self.m, []
        for lo in range(m - 2):
            for block in itertools.combinations(self.alts, 3):
                rest = [a for a in self.alts if a not in block]
                for order in itertools.permutations(rest):
                    above, below = order[:lo], order[lo:]
                    cur = list(block); walk = [tuple(cur)]
                    for i in (0, 1, 0, 1, 0):
                        cur[i], cur[i + 1] = cur[i + 1], cur[i]; walk.append(tuple(cur))
                    rk = [tuple(above) + w + tuple(below) for w in walk]
                    out.append(dict(block=block, above=tuple(above), ranks=rk, row=self._winding_row(rk, block)))
        for f in out:  # orient each face so that the dictatorship of its block winds +1
            f["row"] = f["row"] * np.sign(f["row"] @ self.best_of(f["block"]))
        return out

    def _winding_row(self, rk, block):
        """Expected winding on the triangle of the block (orientation fixed afterwards)."""
        row = np.zeros(self.nv)
        x0, y0, z0 = block
        cyc = {x0: y0, y0: z0, z0: x0}
        loop = rk + [rk[0]]
        for p, q in zip(loop, loop[1:]):
            x, y = [u for u, v in zip(p, q) if u != v]  # x lowered, y raised
            o = 1 if cyc[x] == y else -1
            row[self.var(p, x)] += o; row[self.var(q, x)] -= o
        return row / 3

    def top_degree_rows(self):
        """For m = 3 the hexagon itself; for m = 4 the two hexagons on each triangle, the one with the
        fourth alternative below minus the one with it above (cellular degree onto that triangle)."""
        if self.m == 3:
            return [self.faces[0]["row"]]
        rows = {}
        for f in self.faces:
            s = -1 if f["above"] else 1
            rows[f["block"]] = rows.get(f["block"], 0) + s * f["row"]
        return list(rows.values())

    def bottom_degrees(self, p, S):
        """Degrees of p on all faces where S occupies the bottom block."""
        m, k = self.m, len(S)
        rest = [a for a in self.alts if a not in S]
        if k == m:
            return [float(t @ p) for t in self.top_degree_rows()]
        if k == 1:
            return [p[self.var(top + S, S[0])] for top in itertools.permutations(rest)]
        if k == 2:
            return [p[self.var(top + S, S[0])] - p[self.var(top + S[::-1], S[0])]
                    for top in itertools.permutations(rest)]
        return [float(f["row"] @ p) for f in self.faces
                if set(f["block"]) == set(S) and len(f["above"]) == m - 3]

    def coords(self, p):
        V0, D = self.V[0], (self.V[1:] - self.V[0]).T
        lam = np.linalg.lstsq(D, p - V0, rcond=None)[0]
        return np.concatenate([[1 - lam.sum()], lam]), np.linalg.norm(D @ lam - (p - V0))

    def lp(self, c, extra=()):
        A = np.vstack([self.A] + [-np.array(r) for r in extra]) if extra else self.A
        b = np.concatenate([self.b, np.zeros(len(extra))]) if extra else self.b
        return linprog(c, A_ub=A, b_ub=b, A_eq=self.E, b_eq=self.e, bounds=(0, 1), method="highs")


def part1_2(ov):
    V0, D = ov.V[0], (ov.V[1:] - ov.V[0]).T
    rank = np.linalg.matrix_rank(D)
    Q, _ = np.linalg.qr(D)
    U, s, _ = np.linalg.svd(np.eye(ov.nv) - Q @ Q.T)
    N = U[:, s > 0.5]
    off = 0.0
    for k in range(N.shape[1]):
        for sg in (1, -1):
            r = ov.lp(-sg * N[:, k])
            off = max(off, abs(-r.fun - sg * N[:, k] @ V0))
    print(f"Part 1, {ov.m} alternatives: {len(ov.V)} rules 'best of S', affine rank {rank}; largest distance of "
          f"an SD-strategy-proof lottery from their affine hull: {off:.1e}")
    P = np.linalg.pinv(D)
    funcs = [(P[i], -P[i] @ V0) for i in range(len(ov.V) - 1)] + [(-P.sum(0), 1 + P.sum(0) @ V0)]
    dim2 = [f["row"] for f in ov.faces]
    for label, extra in (("SD-strategy-proof", ()), ("and windings of dimension 2 >= 0", dim2),
                         ("and top degrees >= 0", dim2 + ov.top_degree_rows())):
        worst = min(ov.lp(a, extra).fun + c0 for a, c0 in funcs)
        print(f"Part 2, {ov.m} alternatives, {label}: smallest coefficient {worst + 0:.4f}")


def part3(ov, trials=200, seed=1):
    rng = np.random.default_rng(seed)
    worst = {}
    for _ in range(trials):
        p = ov.lp(rng.normal(size=ov.nv)).x
        c, res = ov.coords(p)
        for S, cS in zip(ov.subsets, c):
            d = max(abs(x - cS) for x in ov.bottom_degrees(p, S))
            worst[len(S)] = max(worst.get(len(S), 0), d)
    print(f"Part 3, {ov.m} alternatives: largest |c_S - degree on a face with S at the bottom| by |S|, "
          f"{trials} random vertices: {{{', '.join(f'{k}: {v:.1e}' for k, v in sorted(worst.items()))}}}")


def part4(ov):
    degs = []
    for k in range(ov.m):
        v = ov.rule(lambda r: r[k])
        degs.append(sorted({round(float(t @ v), 6) for t in ov.top_degree_rows()}))
    print(f"Part 4, {ov.m} alternatives: top degrees of the positional rules (one value on every face): {degs}")


def neutral(trials=20000, seed=0):
    rng = np.random.default_rng(seed)
    for m in (3, 4, 5, 6):
        B = np.array([[comb(m - i, j - 1) / comb(m, j) for j in range(1, m + 1)] for i in range(1, m + 1)])
        bad, newton = 0, 0.0
        for _ in range(trials):
            w = np.sort(rng.dirichlet(np.ones(m) * 0.7))[::-1]
            mixture = (np.linalg.solve(B, w) >= -1e-12).all()
            d, ok = w.copy(), True
            for _k in range(m - 1):
                d = d[:-1] - d[1:]; ok &= bool((d >= -1e-12).all())
            bad += mixture != ok
            c = np.linalg.solve(B, w)
            for j in range(1, m + 1):
                d = w.copy()
                for _k in range(j - 1):
                    d = d[:-1] - d[1:]
                newton = max(newton, abs(c[j - 1] / comb(m, j) - d[-1]))
        print(f"Part 4, neutral lotteries, {m} alternatives: 'mixture of deterministic rules' and 'all finite "
              f"differences non-negative' disagree on {bad} of {trials} random weight vectors; Newton's formula "
              f"for the coefficients holds to {newton:.1e}")


if __name__ == "__main__":
    for m in (3, 4):
        ov = OneVoter(m)
        part1_2(ov); part3(ov); part4(ov)
    neutral()
