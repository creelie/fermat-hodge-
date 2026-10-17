# Summary of an A_v_w_e file (chains.py output): number of configurations with
# 2-part >= 16 or 3-part >= 27, split by (J >= 4, I >= 3), chain length and move
# names, and whether the chain is direct (at most |B| - 2 elements) or lowering.
import sys, re, math
from collections import Counter
for fn in sys.argv[1:]:
    m=re.match(r'A_(\d+)_(\d+)_(\d+)\.txt', fn.split('/')[-1]); v,w,e=map(int,m.groups())
    def vp(n,p):
        k=0
        while n%p==0: n//=p; k+=1
        return k
    cur=None; recs=[]
    for line in open(fn):
        if not line.strip(): continue
        if not line.startswith(' '):
            B=[tuple(map(int,t.split('/'))) for t in line.split()]
            cur=[B,[],None]; recs.append(cur)
        elif 'NO CHAIN' in line: cur[2]='none'
        else:
            name=line.split()[0]; fin=line.split('->')[1].split()
            cur[1].append(name); cur[2]=len(fin)
    st=Counter()
    for B,moves,fin in recs:
        J=max(vp(o,2) for x,o in B); I=max(vp(o,3) for x,o in B)
        key=('J>=4' if J>=4 else '')+('I>=3' if I>=3 else '')
        kind='none' if fin=='none' else ('direct' if fin<=len(B)-2 else 'lowering')
        st[(key,'+'.join(moves),kind)]+=1
    print(fn,len(recs))
    for k in sorted(st): print('   ',k,st[k])
