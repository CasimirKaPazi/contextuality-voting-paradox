"""BTR-plurality in the smooth model of irv_smooth.py (*BTR and Instant Runoff*, Section 5): the same
Dirichlet beliefs, ballot weight, poll dynamics, starting polls and settling test, with the winner of
BTR-plurality in place of the IRV winner.  For each profile (101 voters, 40 per model) it records
whether some settled run elects a candidate other than the Condorcet winner, and whether no run
settles.  Run: python3 btr_smooth.py MODEL PRECISION PROFILES (for instance ic 85 40); about half an
hour per call on one core.
"""
import sys, itertools
import numpy as np
from irv_smooth import RANK, FIRST, ABOVE, irv_winner, inversions, sincere, starts, condorcet_winner, profile
def btr_winner(S):
    f=np.stack([S[:,FIRST==c].sum(1) for c in range(3)],1)
    order=np.argsort(f,1)  # lowest first
    K=len(S); W=np.empty(K,int)
    b,m,t=order[:,0],order[:,1],order[:,2]
    pref=np.einsum('kb,xyb->kxy',S,ABOVE)  # pref[k,x,y]=share ranking x above y
    idx=np.arange(K)
    s=np.where(pref[idx,b,m]>pref[idx,m,b],b,m)
    W=np.where(pref[idx,s,t]>pref[idx,t,s],s,t)
    return W
WIN={'irv':irv_winner,'btr':btr_winner}
def best_replies(U,v,method,s,delta,rng,K):
    S=rng.dirichlet(s*v+0.5,size=K); win=WIN[method]
    P=np.zeros((6,3))
    for b in range(6):
        T=S.copy(); T[:,b]+=delta; P[b]=np.bincount(win(T),minlength=3)/K
    EU=U@P.T; best=[]
    for i,u in enumerate(U):
        cand=np.where(EU[i]>=EU[i].max()-1e-12)[0]; best.append(min(cand,key=lambda b:inversions(u,b)))
    return np.array(best)
def run(U,method,v,s,rng,delta=0.002,lam=0.05,T=300,K=6000):
    win=WIN[method]; vs,ws=[],[]
    for _ in range(T):
        b=best_replies(U,v,method,s,delta,rng,K); v=(1-lam)*v+lam*np.bincount(b,minlength=6)/len(U)
        vs.append(v.copy()); ws.append(int(win(v[None])[0]))
    settled=len(set(ws[-100:]))==1 and np.abs(vs[-1]-vs[-101]).max()<0.03
    return settled,ws[-1],v
if __name__=='__main__':
    model=sys.argv[1]; s=float(sys.argv[2]); profiles=int(sys.argv[3])
    rng=np.random.default_rng(11); st=dict(cw=0,other=0,none=0,no_cw=0,no_cw_settled=0)
    for p in range(profiles):
        U=profile(model,101,rng); c=condorcet_winner(U); r=np.random.default_rng(100+p); won=set()
        for k,v0 in enumerate(starts(U,'irv',r)):
            settled,w,v=run(U,'btr',v0.copy(),s,np.random.default_rng(1000*p+k))
            if settled: won.add(w)
        if c is None: st['no_cw']+=1; st['no_cw_settled']+=bool(won)
        else: st['cw']+=1; st['none']+= not won; st['other']+= any(w!=c for w in won)
    print(model,s,st,flush=True)
