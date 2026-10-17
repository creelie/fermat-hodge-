forkB scripts (local step at a prime e' = p, D | 72); see notes/sec14-prime.md.
prop.c         propagation search, formal (p = 0) or modulo p >= 29: prop V W p [maxn]
locDm.c        multipass variant of m6/locD.c (table split in K hash classes): locDm p v w K
cmp.py         compare prop and locD lists up to units: cmp.py N prop_file locD_file
fchain.py      chains (lchain.py semantics, moves T, sigma_3) in CRT coordinates, formal or mod p >= 29
randtest.py    random cross-check of fchain.py against m6/lchain.py
levelchain.py  chains at level lcm(D_B, 6) p for each configuration (backend lchain or fchain)
specialize.py  compare prop mod p with the reductions of the formal list
chainprimes.py primes where two elements of a formal chain collide modulo p
cand.py        candidate exceptional primes: 2^a 3^b = +-1 mod p, |a| <= A, |b| <= B
direct.py      direct check at a list of primes (prop, specialize, levelchain)
F_V_W.txt      formal configurations at D = 2^V 3^W;  FC_3_2.txt their chains at D = 72
run23.sh, runsmall.sh, rundirect.sh, runx.sh, runy.sh  the runs behind Q7 and Q4 (see notes/sec14-prime.md)
Pcand.txt      P_cand (cand.py 18 12);  direct.log  one line per prime of P_cand (Q7(a))
CP.txt         chainprimes.py on the formal chains (fdump/)
L_3_2_23.txt   locDm at p = 23, D = 72;  LC_3_2_p.txt  levelchain (lchain backend) for p = 5..23
X_*.txt        prop vs locD at p = 29 (D = 36, 72);  Y/  checks at p = 541, 739;  ex23/, ex31/  chains of the two extra configurations
P_V_W_p.txt    prop modulo p (Q4 checks);  modp/ (per-prime outputs of direct.py) is not mirrored (1188 files)
