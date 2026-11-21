import sys, random
from diag2 import rows_of, dictator
from recipes_core import works_PQ
from itertools import product, permutations, combinations
mode=sys.argv[1]; m1, m2, k = map(int, sys.argv[2:5])
outs = "abcdefg"[:k]; prefs = list(permutations(outs))
def forces(R, A): return any(set(r) <= A for r in R)
def tight(g):
    R1 = rows_of(g, m1, m2, 0); R2 = rows_of(g, m1, m2, 1)
    for r in range(0, k+1):
        for A in combinations(outs, r):
            A = set(A)
            if not forces(R1, A) and not forces(R2, set(outs) - A): return False
    return True
def gen():
    if mode=="all":
        for g in product(outs, repeat=m1*m2):
            if g[0]=='a': yield g
    else:
        rnd=random.Random(int(sys.argv[5]))
        for _ in range(int(sys.argv[6])): yield tuple(rnd.choice(outs) for _ in range(m1*m2))
tot=0; h1=0; h2=0; ex1=None; ex2=None
for g in gen():
    if set(g)!=set(outs) or dictator(g,m1,m2,outs) or not tight(g): continue
    tot+=1
    ok1=False; ok2=False
    for i in (0,1):
        R=rows_of(g,m1,m2,i)
        for x in outs:
            if forces(R,{x}): continue
            Ps=[P for P in prefs if P[0]==x]; Qs=[Q for Q in prefs if Q[-1]==x]
            res=[works_PQ(R,P,Q) for P in Ps for Q in Qs]
            if any(res): ok1=True
            if all(res): ok2=True
    if not ok1:
        h1+=1; ex1=ex1 or g
    if not ok2:
        h2+=1; ex2=ex2 or g
print(mode,m1,m2,k,"tight nondict",tot,"H1 fails",h1,"H2(all P,Q) fails",h2)
for e in (ex1,ex2):
    if e: print([" ".join(e[a*m2:(a+1)*m2]) for a in range(m1)])
