"""Stage 2 in bits for BTR-plurality and instant runoff in the smooth model (*Instant Runoff and BTR-Plurality*,
Section 6).  Both methods take ranked ballots, so a poll (a vector of expected ballot shares) is the
same object for both: the ballots are compared at the resting IRV poll, at the resting BTR poll
(each reached from the sincere ballots) and with each method at its own poll.  Entropies over 4000
voters from the profile's culture, as in irv_bits.py.  Run: python3 btr_bits.py MODEL PRECISION;
about a quarter of an hour per call.
"""
import sys
import numpy as np
from btr_smooth import best_replies, run
from irv_smooth import sincere, FIRST
from irv_bits import H, Hc, voters
def main(model,s,profiles=20):
    rng=np.random.default_rng(5); R=[]
    for p in range(profiles):
        cand=rng.normal(size=(3,2)); U=voters(model,rng,101,cand); X=voters(model,rng,4000,cand); rk=np.random.default_rng(p)
        si,wi,vi=run(U,'irv',sincere(U,'irv'),s,rk); sb,wb,vb=run(U,'btr',sincere(U,'irv'),s,rk)
        rank=[tuple(np.argsort(-u)) for u in X]
        for name,ok,v in (('IRV poll',si,vi),('BTR poll',sb,vb)):
            if not ok: continue
            bi=list(best_replies(X,v,'irv',s,0.002,rk,20000)); bb=list(best_replies(X,v,'btr',s,0.002,rk,20000))
            R.append((name,H(bi),H(bb),Hc(bb,bi),Hc(bi,bb),Hc(bb,rank),Hc(bi,rank)))
        if si and sb:
            bi=list(best_replies(X,vi,'irv',s,0.002,rk,20000)); bb=list(best_replies(X,vb,'btr',s,0.002,rk,20000))
            R.append(('own polls',H(bi),H(bb),Hc(bb,bi),Hc(bi,bb),Hc(bb,rank),Hc(bi,rank)))
    for name in ('IRV poll','BTR poll','own polls'):
        A=np.array([r[1:] for r in R if r[0]==name])
        print(f"{model} s={s} {name:9s} n={len(A)} H(IRV) {A[:,0].mean():.2f} H(BTR) {A[:,1].mean():.2f} H(BTR|IRV) {A[:,2].mean():.3f} (zero {(A[:,2]<1e-9).sum()}) H(IRV|BTR) {A[:,3].mean():.3f} (zero {(A[:,3]<1e-9).sum()}) H(BTR|rank) {A[:,4].mean():.3f} H(IRV|rank) {A[:,5].mean():.3f}",flush=True)
if __name__ == '__main__':
    main(sys.argv[1], float(sys.argv[2]))
