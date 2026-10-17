# Block pattern search (def:blockpattern of e84hc) by linear programming:
# max sum(lam) s.t. sum lam_l e_l <= 1 (each coordinate), lam >= 0,
# columns e in {0..B}^n with a zero and a positive entry and e.alpha = 0 mod m.
# A value > 1 gives a block pattern (rem:uniruled). usage: bp.py m B a1 ... an
import sys, itertools
import numpy as np
from scipy.optimize import linprog
m=int(sys.argv[1]); B=int(sys.argv[2]); a=list(map(int,sys.argv[3:])); n=len(a)
cols=[e for e in itertools.product(range(B+1),repeat=n) if min(e)==0 and max(e)>0 and sum(x*y for x,y in zip(e,a))%m==0]
for k in range(n):
    e=[0]*n; e[k]=m; cols.append(tuple(e))
A=np.array(cols,dtype=float).T
res=linprog(-np.ones(len(cols)),A_ub=A,b_ub=np.ones(n),bounds=(0,None),method='highs')
val=-res.fun
print("m=%d alpha=%s columns=%d LP value=%.6f"%(m,a,len(cols),val))
if val>1+1e-9:
    for l,x in enumerate(res.x):
        if x>1e-9: print("  col",cols[l],"lam=%.6f"%x)
