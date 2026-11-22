"""Atoms describing the safe lines, relative to the saddle index q of the opposed game; which pairs
of atoms never occur together?"""
import random, itertools, collections, sys
from sg import matrix
from k3_chain import T, forces, tt
from chain_pairs import safe_lines, valid
from chain_pairs import saddle_index
def atoms(Ri, Ro, P, k):
    a, c = P[0], P[-1]; rP = P[::-1]; Ps = (a,) + rP[:-1]; rPs = (c,) + P[:-1]
    pos = {u: n for n, u in enumerate(P)}; q = saddle_index(Ri, P); A = set()
    cmp = lambda x: "<" if x < q else ("=" if x == q else ">")
    for r in safe_lines(Ri, P, rP): A.add("r1" + ("a" if a in r else "-"))
    for s in safe_lines(Ro, rP, P): A.add("s2" + ("c" if c in s else "-"))
    for r in safe_lines(Ri, Ps, rP):
        if c in r: A.add("gamma")
        else: A.add("delta" + cmp(pos[max(r, key=lambda u: pos[u])]))
    for s in safe_lines(Ro, rPs, P):
        if a in s: A.add("alpha")
        else: A.add("beta" + cmp(pos[min(s, key=lambda u: pos[u])]))
    return frozenset(A)
if __name__ == "__main__":
    random.seed(19); seen = collections.Counter()
    for k in (4, 5):
        g = 0
        while g < (2000 if k < 5 else 500):
            n = random.randint(k, k + 7)
            p = tuple(random.randrange(2) for _ in range(n)); o = tuple(random.randrange(k) for _ in range(n)); z = random.randrange(k)
            R = matrix(p, o, z, 0)
            if not valid(R, k): continue
            g += 1
            for Ri, Ro in ((R, T(R)), (T(R), R)):
                for a, c in itertools.permutations(range(k), 2):
                    if forces(Ri, a) or forces(Ro, c): continue
                    for mid in itertools.permutations([u for u in range(k) if u not in (a, c)]):
                        seen[atoms(Ri, Ro, (a,) + mid + (c,), k)] += 1
    allat = sorted(set().union(*seen))
    print("atoms:", allat)
    pairs = collections.Counter()
    for S, n in seen.items():
        for x, y in itertools.combinations(sorted(S), 2): pairs[(x, y)] += n
    print("pairs never together:", [p for p in itertools.combinations(allat, 2) if pairs[p] == 0])
    print("sets containing r1, s2, a twin-i line and a twin-o line:",
          [sorted(S) for S in seen if any(x.startswith("r1") for x in S) and any(x.startswith("s2") for x in S)
           and S & {"gamma", "delta<", "delta=", "delta>"} and S & {"alpha", "beta<", "beta=", "beta>"}])
    pickle_out = {tuple(sorted(S)): n for S, n in seen.items()}
    import pickle; pickle.dump(pickle_out, open("chain_atoms.pkl", "wb"))
