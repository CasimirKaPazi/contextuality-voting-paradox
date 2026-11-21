import sys, collections
from itertools import product, permutations, combinations
from diag2 import rows_of, dictator
from recipes_core import works_PQ
m1,m2,k=map(int,sys.argv[1:4]); outs="abcdefg"[:k]
def TT(g):
    for r1,r2 in combinations(range(m1),2):
        for c1,c2 in combinations(range(m2),2):
            A,B,C,D=g[r1*m2+c1],g[r1*m2+c2],g[r2*m2+c1],g[r2*m2+c2]
            if not(A==B or C==D or A==C or B==D): return False
    return True
def reduce(g):
    R=list(range(m1)); C=list(range(m2)); ch=True
    while ch and R and C:
        ch=False
        for r in R:
            if len({g[r*m2+c] for c in C})==1: R.remove(r); ch=True; break
        if ch: continue
        for c in C:
            if len({g[r*m2+c] for r in R})==1: C.remove(c); ch=True; break
    return R,C
stat=collections.Counter(); ex={}
for g in product(outs,repeat=m1*m2):
    if set(g)!=set(outs) or g[0]!='a' or dictator(g,m1,m2,outs) or not TT(g): continue
    R,C=reduce(g)
    if not R or not C: continue
    core=tuple(g[r*m2+c] for r in R for c in C); co=sorted(set(core))
    cr=rows_of(core,len(R),len(C),0)
    good=[t for t in permutations(co) if any(works_PQ(cr,t,q) for q in permutations(co) if q[-1]==t[0])]
    others=tuple(o for o in outs if o not in co)
    for i in (0,1):
        Rw=rows_of(g,m1,m2,i)
        for (x,y,z) in good:
            if any(all(v==x for v in r) for r in Rw): continue
            P=(x,y,z)+others
            vari={"Q=z y O x":(z,y)+others+(x,), "Q=z y rev(O) x":(z,y)+others[::-1]+(x,),
                  "Q=O z y x":others+(z,y,x), "Q=y z O x":(y,z)+others+(x,), "Q=z O y x":(z,)+others+(y,x)}
            for name,Q in vari.items():
                w=works_PQ(Rw,P,Q); stat[(name,w)]+=1
                if not w: ex.setdefault(name,g)
print(m1,m2,k,sorted(stat.items()))
for n,g in ex.items(): print(n,[" ".join(g[a*m2:(a+1)*m2]) for a in range(m1)])
