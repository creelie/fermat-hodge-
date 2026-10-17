# Generates fig_aoki.tex: the products of distinct elements of P = {4,3,5,7}
# dividing 2^a 3^b 5^c 7^d, ranked by the number of factors; the products of an
# even number of factors (> 1) form Q(M) and carry Aoki's classes.
import itertools, math
P=[4,3,5,7]
ang={4:45,3:135,5:225,7:315}
Rx,Ry,H=2.9,0.6,2.05
def pos(S):
    k=len(S)
    if k in (0,4): return (0.0,H*k)
    if k==1: a=ang[S[0]]; r=1.0
    elif k==3:
        miss=[p for p in P if p not in S][0]; a=(ang[miss]+180)%360; r=1.0
    else:
        a1,a2=sorted(ang[p] for p in S)
        if a2-a1==180: a=a1+90 if S==(4,5) or set(S)=={4,5} else a1+90+180; r=0.42
        elif a2-a1==270: a=0; r=1.0
        else: a=(a1+a2)/2; r=1.0
    return (Rx*r*math.cos(math.radians(a)), H*k+Ry*r*math.sin(math.radians(a)))
subsets=[tuple(S) for k in range(5) for S in itertools.combinations(P,k)]
def name(S): return str(math.prod(S)) if S else '1'
out=[]
out.append(r'''\documentclass[tikz,border=6pt]{standalone}
\usepackage{lmodern}
\usepackage{amsmath}
\usetikzlibrary{calc}
\definecolor{ablue}{RGB}{38,84,160}
\definecolor{sorange}{RGB}{214,110,22}
\definecolor{plane}{RGB}{232,235,241}
\begin{document}
\begin{tikzpicture}''')
for k in range(5):
    if k in (0,4): continue
    out.append(r'\fill[plane,opacity=0.6] (0,%.3f) ellipse[x radius=%.2f,y radius=%.2f];'%(H*k,Rx+0.55,Ry+0.25))
    out.append(r'\draw[gray!45,line width=0.3pt] (0,%.3f) ellipse[x radius=%.2f,y radius=%.2f];'%(H*k,Rx+0.55,Ry+0.25))
    out.append(r'\node[font=\scriptsize,gray!60!black,anchor=west] at (%.2f,%.3f) {%s};'%(Rx+0.75,H*k,['','one factor','two factors','three factors',''][k]))
out.append(r'\node[font=\scriptsize,gray!60!black,anchor=west] at (%.2f,%.3f) {four factors};'%(Rx+0.75,4*H))
out.append(r'\node[font=\scriptsize,gray!60!black,anchor=west] at (%.2f,%.3f) {no factor};'%(Rx+0.75,0))
# edges
for S in subsets:
    for T in subsets:
        if len(T)==len(S)+1 and set(S)<set(T):
            (x1,y1),(x2,y2)=pos(S),pos(T)
            depth=(y1-H*len(S))+(y2-H*len(T))
            col='gray!35' if depth>0.3 else 'gray!70'
            out.append(r'\draw[%s,line width=0.6pt] (%.3f,%.3f) -- (%.3f,%.3f);'%(col,x1,y1,x2,y2))
for S in subsets:
    x,y=pos(S); k=len(S)
    c='gray!60' if k==0 else ('sorange' if k%2==0 else 'ablue')
    out.append(r'\shade[ball color=%s] (%.3f,%.3f) circle (0.12);'%(c,x,y))
    # label to the right of the ball
    out.append(r'\node[font=\footnotesize,anchor=south west,inner sep=1pt,fill=white,fill opacity=0.8,text opacity=1] at (%.3f,%.3f) {$%s$};'%(x+0.08,y+0.06,name(S)))
out.append(r'''\end{tikzpicture}
\end{document}''')
open('fig_aoki.tex','w').write('\n'.join(out)+'\n')
