from math import gcd
m=35; a=(1,2,16,21,30); b=(17,22,31)
U=[t for t in range(1,m) if gcd(t,m)==1]
br=lambda v,t: sum((t*x)%m for x in v)//m
assert all(sum((t*x)%m for x in a)%m==0 and sum((t*x)%m for x in b)%m==0 for t in U)
print('t   ', [t for t in U if t<m/2])
print('<ta>', [br(a,t) for t in U if t<m/2])
print('<tb>', [br(b,t) for t in U if t<m/2])
print('all sums 4:', all(br(a,t)+br(b,t)==4 for t in U))
beta=sorted(a+b); print('beta',beta,'pairs',[(x,y) for i,x in enumerate(beta) for y in beta[i+1:] if (x+y)%m==0])
print('square 1:', [x for x in beta if x*x%m==1])
print('balanced:', len({sum((t*x)%m for x in beta) for t in U})==1, sum(beta))
# stabiliser of alpha (dimension of M_alpha)
print('stab', [t for t in U if sorted((t*x)%m for x in a)==sorted(a)])
# alpha alone in H^{2,1}? and is beta containing pair? also orders
print('5b,5a',[ (5*x)%m for x in a])
for t in U:
    if t<m/2: print(t, [(t*x)%m for x in a], sum((t*x)%m for x in a), [(t*x)%m for x in b], sum((t*x)%m for x in b))
