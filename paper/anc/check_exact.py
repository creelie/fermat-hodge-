from fractions import Fraction as F
from itertools import product

orbit_dimensions=set()
for t in product(range(11),repeat=3):
    orbit={t,t[1:]+t[:1],t[2:]+t[:2]}
    dimension=sum((a+1)*(b+1)*(c+1) for a,b,c in orbit)
    if dimension<=10:
        orbit_dimensions.add((tuple(sorted(orbit)),dimension))
expected={(((0,0,0),),1),(((1,1,1),),8),(((0,0,1),(0,1,0),(1,0,0)),6),(((0,0,2),(0,2,0),(2,0,0)),9)}
assert orbit_dimensions==expected
print('PASS complete small highest-weight orbit enumeration')
