# Brute-force check of Lemma S on product grids K_1 x ... x K_r:
# a function split along (K_i) is f = sum_i g_i, g_i not depending on coordinate i.
# Enumerate small integer g_i (normalised), keep nonzero f of mass <= 8, classify.
import itertools, sys
from collections import Counter
def check(sizes, rng):
    r=len(sizes); pts=list(itertools.product(*[range(n) for n in sizes]))
    others=[ [j for j in range(r) if j!=i] for i in range(r)]
    # g_i is a function of the other coordinates; for r=2 that is one coordinate.
    assert r==2
    shapes=Counter(); bad=[]
    for a in itertools.product(rng, repeat=sizes[1]):      # g_0 depends on coord 1
        for b in itertools.product(rng, repeat=sizes[0]):  # g_1 depends on coord 0
            if b[0]!=0: continue
            f={p:a[p[1]]+b[p[0]] for p in pts}
            m=sum(abs(v) for v in f.values())
            if m==0 or m>8: continue
            shapes[classify(f,sizes)]+=1
    return shapes
def lines(sizes):
    L=[]
    for i,n in enumerate(sizes):
        for rest in itertools.product(*[range(sizes[j]) for j in range(len(sizes)) if j!=i]):
            pts=[]
            for c in range(n):
                p=list(rest); p.insert(i,c); pts.append(tuple(p))
            L.append((i,frozenset(pts)))
    return L
def classify(f,sizes):
    supp={p:v for p,v in f.items() if v}
    vals=set(supp.values())
    for i,L in lines(sizes):
        if set(supp)==L and len(vals)==1:
            v=vals.pop(); return 'line%d*%d'%(sizes[i],abs(v))
    LL=lines(sizes)
    for (i,L),(j,L2) in itertools.combinations(LL,2):
        for s in (1,-1):
            for s2 in (1,-1):
                g={p:0 for p in f}
                for p in L: g[p]+=s
                for p in L2: g[p]+=s2
                if g==f:
                    return 'two%s:%d,%d meet%d'%('' if s==s2 else 'opp',sizes[i],sizes[j],len(L&L2))
    return 'OTHER'
print('K sizes (4,6):',dict(check((4,6),range(-2,3))))
print('K sizes (5,6):',dict(check((5,6),range(-2,3))))
print('K sizes (4,7):',dict(check((4,7),range(-2,3))))
