"""Bottom-two runoff with plurality order (BTR-plurality) against instant runoff, three candidates, in
the corner (*Instant Runoff and BTR-Plurality*, Sections 3 and 4).

BTR-plurality orders the candidates once by first preferences (top T, middle M, bottom B); the
bottom two meet in a pairwise runoff on the full rankings, the survivor meets T, and the winner of
that runoff is elected.  A poll names T, M, B, the expected winner S of the first runoff (the other
is o), the expected winner L of S against T, and Wo, the winner of o against T.  Two pivot events:

  F   S and T tied in the final runoff: a ballot counts for whichever of S, T it ranks higher;
  E'  M and B tied in the first runoff: ranking S above o makes the winner L, o above S makes it Wo.

Weights of E' relative to F as in irv_three.py ('F', 1, 'E'); remaining ties broken towards the
sincere ranking.  A poll is self-confirming if the strategic ballots reproduce the first-preference
order T > M > B, S beating o, L winning S against T and Wo winning o against T (all strictly).

Checked on 300 random profiles per model (101 voters): how often a self-confirming poll elects a
candidate other than the Condorcet winner, how often there is none, whether there is one without a
Condorcet winner, and how many best replies change the first preference or rank the finalists S, T
against the voter's preference.  About four and a half minutes.
"""
import itertools, random
from irv_three import RANKINGS, inversions, above, condorcet_winner, profile
C=(0,1,2)
def btr_polls():
    for T,M,B in itertools.permutations(C):
        for S in (M,B):
            o=B if S==M else M
            for L in (S,T):
                for Wo in (o,T):
                    yield (T,M,B,S,L,Wo)
def best_btr(u,P,t):
    T,M,B,S,L,Wo=P; o=B if S==M else M
    sinc=tuple(sorted(C,key=lambda c:-u[c]))
    def dF(b):
        hi,lo=(S,T) if b.index(S)<b.index(T) else (T,S); return (u[hi]-u[lo])/2
    def dE(b):
        return (u[L]-u[Wo])/2 if b.index(S)<b.index(o) else (u[Wo]-u[L])/2
    if t=='F': key=lambda b:(round(dF(b),12),round(dE(b),12),-inversions(b,sinc))
    elif t=='E': key=lambda b:(round(dE(b),12),round(dF(b),12),-inversions(b,sinc))
    else: key=lambda b:(round(dF(b)+t*dE(b),12),-inversions(b,sinc))
    return max(RANKINGS,key=key)
def btr_sc(U,t):
    out=[]
    for P in btr_polls():
        T,M,B,S,L,Wo=P; o=B if S==M else M
        Bal=[best_btr(u,P,t) for u in U]
        f=[sum(1 for b in Bal if b[0]==c) for c in C]
        if not f[T]>f[M]>f[B]: continue
        a,b=above(Bal,S,o)
        if not a>b: continue
        x,y=above(Bal,S,T)
        if x==y or (S if x>y else T)!=L: continue
        x,y=above(Bal,o,T)
        if x==y or (o if x>y else T)!=Wo: continue
        out.append(P)
    return out
def main():
  for model in ('ic','spatial'):
      for t in ('F',1,'E'):
          rng=random.Random(7); St=dict(cw=0,none=0,other=0,nocw=0,nocw_some=0,ballots=0,mis_first=0,mis_fin=0)
          for k in range(300):
              U=profile(model,101,rng); c=condorcet_winner(U); sc=btr_sc(U,t); won={P[4] for P in sc}
              for P in btr_polls():
                  T,M,B,S,L,Wo=P
                  for u in U:
                      b=best_btr(u,P,t); St['ballots']+=1
                      St['mis_first']+= b[0]!=max(C,key=lambda x:u[x])
                      St['mis_fin']+= (b.index(S)<b.index(T))!=(u[S]>u[T])
              if c is None: St['nocw']+=1; St['nocw_some']+=bool(sc)
              else: St['cw']+=1; St['none']+= not sc; St['other']+= any(w!=c for w in won)
          print(model,t,St)


if __name__ == '__main__':
    main()
