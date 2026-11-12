# mumford_residual.jl -- port of the round programs r2-MUM/r2_lattice.py and
# r2-MUM/r2_disc.py: the residual case L = K (sextic CM field without imaginary
# quadratic subfield) at a CM point t0 of a Mumford family.
#
# Part 1  (r2_lattice.py) characters of the Hodge torus U_L x U_K, X^* = Z^3 + Z^3:
#         Galois orbits (8 for X, 6 for B_1), rank 6 of the Hodge torus for P = A3, S3.
#   A     X_t0 is of Weil type for the quadratic subfield k* of the reflex field
#         (parity character), Hodge monomials on X and X^2 are pairs x Weil quadruples.
#   B     the lattices in X^*(T_E) = Z^20 (Smith invariants): Lambda_H0 has rank 13,
#         Lambda_1 rank 10, <pairs, mixed quadruples> = Lambda_H0.
#   C     dimensions of Hodge classes and of the ring R_1 on X^a x B_1 x B_2.
#   D     CM fields E of degree 12 with K in E in K.K*, Weil type of X^3 x B_1^2 x B_2^2.
# Part 2  (r2_disc.py) three explicit fields K = F(sqrt(-delta)): N(delta), the field
#         k* = Q(sqrt(-N(delta))), the quartic g of K*+, disc(g)/d_F a square, and
#         elements a of K*+ with the required signs and N(a) d_F a norm from k*
#         (polarisations of discriminant 1), with an explicit norm representation.
#
# Part 1 is integer arithmetic.  In Part 2 the quartic g, its discriminant, the norms and
# the Hilbert symbols are exact; the Python obtains g by rounding floating-point products,
# here g is computed from the elementary symmetric functions of delta.  Signs at the real
# places are evaluated with 256-bit BigFloat (the Python uses Float64).  "delta is not in
# Q^x F^x2" is certified exactly by a prime of degree 1 of F at which delta N(delta) is a
# non-residue (the Python tests a floating-point criterion).
# Run: julia --startup-file=no mumford_residual.jl

const NPASS = Ref(0); const NFAIL = Ref(0)
function check(name, ok)
    ok ? (NPASS[] += 1) : (NFAIL[] += 1)
    println(ok ? "PASS " : "FAIL ", name)
end

# ================================================================ Part 1
const Ch = NTuple{6,Int}
const MU = (0, 0, 1, 1, 1, 0)
dot6(a, b) = sum(a .* b)
holo(ch) = dot6(ch, MU) > 0
const SIGNS = [(a, b, c) for a in (1, -1) for b in (1, -1) for c in (1, -1)]
const Xch = Ch[(s..., 0, 0, 0) for s in SIGNS]
function unit(i, a, b)                 # i in 0:2
    v = zeros(Int, 6); v[i+1] = a; v[4+i] = b; Tuple(v)::Ch
end
const B1ch = Ch[unit(i, u, u) for i in 0:2 for u in (1, -1)]
const B2ch = Ch[unit(i, -u, u) for i in 0:2 for u in (1, -1)]
const ALL = vcat([(:X, c) for c in Xch], [(:B1, c) for c in B1ch], [(:B2, c) for c in B2ch])
const IDX = Dict(v => k for (k, v) in enumerate(ALL))
negc(c) = .-c

check("all 20 characters have |<ch, mu>| = 1", all(abs(dot6(c, MU)) == 1 for (f, c) in ALL))
check("B_1 holomorphic characters are (e_i; f_i)",
      [c for c in B1ch if holo(c)] == [(1, 0, 0, 1, 0, 0), (0, 1, 0, 0, 1, 0), (0, 0, 1, 0, 0, 1)])
check("B_2 holomorphic characters are (-e_1;f_1), (-e_2;f_2), (e_3;-f_3)",
      [c for c in B2ch if holo(c)] == [(-1, 0, 0, 1, 0, 0), (0, -1, 0, 0, 1, 0), (0, 0, 1, 0, 0, -1)])

# ---------------------------------------------------------------- Galois action
const GE = Tuple{NTuple{3,Int},NTuple{3,Int}}       # (permutation of 0:2, signs)
gal(P) = GE[(p, e) for p in P for e in SIGNS]
function act(g::GE, ch)
    p, e = g
    out = zeros(Int, 6)
    for j in 1:3
        pj = p[j] + 1
        out[pj] = e[pj] * ch[j]; out[3+pj] = e[pj] * ch[3+j]
    end
    Tuple(out)::Ch
end
const A3 = [(0, 1, 2), (1, 2, 0), (2, 0, 1)]
const S3 = [(0, 1, 2), (0, 2, 1), (1, 0, 2), (1, 2, 0), (2, 0, 1), (2, 1, 0)]

function rank_rational(rows)
    M = [Rational{Int}.(collect(r)) for r in rows]; r = 0
    isempty(M) && return 0
    for c in 1:length(M[1])
        piv = findfirst(i -> M[i][c] != 0, r+1:length(M))
        piv === nothing && continue
        piv += r
        M[r+1], M[piv] = M[piv], M[r+1]
        for i in 1:length(M)
            if i != r + 1 && M[i][c] != 0
                f = M[i][c] / M[r+1][c]; M[i] = M[i] .- f .* M[r+1]
            end
        end
        r += 1
    end
    r
end

for (nm, P, ng) in (("A3", A3, 24), ("S3", S3, 48))
    G = gal(P)
    check("P = $nm: |Gal| = $ng and the three character sets are Galois stable",
          length(G) == ng && all(sort([act(g, c) for c in chs]) == sort(chs) for chs in (Xch, B1ch, B2ch) for g in G))
    orbX = Set(act(g, Xch[1]) for g in G); orbB = Set(act(g, B1ch[1]) for g in G)
    check("P = $nm: orbit of an X-character has 8 elements (octic reflex field)", length(orbX) == 8)
    check("P = $nm: orbit of a B_1-character has 6 elements", length(orbB) == 6)
    orb = sort(collect(Set(act(g, MU) for g in G)))
    check("P = $nm: rank of the Hodge torus = 6", rank_rational(orb) == 6)
end

# ---------------------------------------------------------------- Part A
par(c) = c[1] * c[2] * c[3]
check("A: parity c1 c2 c3 of an X-character transforms by e1 e2 e3 (so it is fixed by an index-2 subgroup; k* in K*)",
      all(par(act(g, c)) == par(c) * prod(g[2]) for P in (A3, S3) for g in gal(P) for c in Xch))
const EV = [c for c in Xch if par(c) == 1]
check("A: iota-eigenspace of k* on H^1(X) has characters (1,1,1),(1,-1,-1),(-1,1,-1),(-1,-1,1)",
      [c[1:3] for c in EV] == [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)])
check("A: the eigenspace has 2 characters of type (1,0) and 2 of type (0,1) (Weil type (2,2))",
      count(holo, EV) == 2 && count(!holo, EV) == 2)
check("A: the four characters sum to 0 (the Weil class is a Hodge class)",
      reduce((a, b) -> a .+ b, EV) == (0, 0, 0, 0, 0, 0))
check("A: characters of wedge^2 of the eigenspace are +-2 e_i",
      sort([(EV[i].+EV[j])[1:3] for i in 1:4 for j in i+1:4]) ==
      sort([(2, 0, 0), (-2, 0, 0), (0, 2, 0), (0, -2, 0), (0, 0, 2), (0, 0, -2)]))

"all Hodge monomials on X^nc: counts by degree, counts of non-products, and whether all are pairs x Weil quadruples"
function brute(nc)
    vs = [c for k in 1:nc for c in Xch]
    cnt = Dict{Int,Int}(); nd = Dict{Int,Int}(); allok = true
    for mask in 0:(1<<length(vs))-1
        d = count_ones(mask)
        isodd(d) && continue
        w = (0, 0, 0, 0, 0, 0); m = Dict{Ch,Int}()
        for i in 1:length(vs)
            if (mask >> (i - 1)) & 1 == 1
                w = w .+ vs[i]; m[vs[i]] = get(m, vs[i], 0) + 1
            end
        end
        w == (0, 0, 0, 0, 0, 0) || continue
        cnt[d] = get(cnt, d, 0) + 1
        net = [get(m, c, 0) - get(m, negc(c), 0) for c in EV]
        allok &= net[1] == net[2] == net[3] == net[4]
        net[1] != 0 && (nd[d] = get(nd, d, 0) + 1)
    end
    cnt, nd, allok
end
let
    cnt, nd, ok = brute(1)
    check("A: X: Hodge monomials by degree 1,4,8,4,1; non-products 2 in degree 4; all = pairs x (Weil quadruple)^m",
          ok && cnt == Dict(0 => 1, 2 => 4, 4 => 8, 6 => 4, 8 => 1) && nd == Dict(4 => 2))
    cnt, nd, ok = brute(2)
    check("A: X^2: Hodge monomials by degree 1,16,132,432,648,432,132,16,1; all = pairs x (Weil quadruple)^m",
          ok && cnt == Dict(0 => 1, 2 => 16, 4 => 132, 6 => 432, 8 => 648, 10 => 432, 12 => 132, 14 => 16, 16 => 1))
    check("A: X^2: non-products by degree 32,128,194,128,32 (degrees 4..12)",
          nd == Dict(4 => 32, 6 => 128, 8 => 194, 10 => 128, 12 => 32))
end

# ---------------------------------------------------------------- integer lattices
"nonzero invariant factors (Smith normal form) of an integer matrix given by rows"
function smith_invariants(rows, ncols)
    rows = [r for r in rows if any(!iszero, r)]
    inv = BigInt[]
    isempty(rows) && return inv
    A = zeros(BigInt, length(rows), ncols)
    for (i, r) in enumerate(rows), j in 1:ncols
        A[i, j] = r[j]
    end
    n, m = size(A); t = 1
    while t <= min(n, m)
        while true
            best = (0, 0)
            for i in t:n, j in t:m
                if A[i, j] != 0 && (best == (0, 0) || abs(A[i, j]) < abs(A[best...]))
                    best = (i, j)
                end
            end
            best == (0, 0) && return inv
            i, j = best
            A[[t, i], :] = A[[i, t], :]; A[:, [t, j]] = A[:, [j, t]]
            p = A[t, t]; done = true
            for i in t+1:n
                if A[i, t] != 0
                    A[i, :] .-= fld(A[i, t], p) .* A[t, :]
                    A[i, t] != 0 && (done = false)
                end
            end
            for j in t+1:m
                if A[t, j] != 0
                    A[:, j] .-= fld(A[t, j], p) .* A[:, t]
                    A[t, j] != 0 && (done = false)
                end
            end
            if done
                bad = 0
                for i in t+1:n
                    if any(A[i, j] % p != 0 for j in t+1:m)
                        bad = i; break
                    end
                end
                bad == 0 && break
                A[t, :] .+= A[bad, :]
            end
        end
        push!(inv, abs(A[t, t])); t += 1
    end
    inv
end
function wvec(mon)
    v = zeros(Int, 20)
    for x in mon
        v[IDX[x]] += 1
    end
    v
end
const tau0 = wvec([(:X, Xch[1]), (:X, negc(Xch[1]))])
const pairs = [wvec([(f, c), (f, negc(c))]) .- tau0 for (f, c) in ALL]
const weilq = wvec([(:X, c) for c in EV]) .- 2 .* tau0
const mixed = Tuple{Int,Int,Vector{Int}}[]
mixed_ok = true
for i in 0:2, u in (1, -1), s in Xch
    s[i+1] == u || continue
    s2 = (ntuple(j -> j == i + 1 ? 2u - s[j] : -s[j], 3)..., 0, 0, 0)
    mon = [(:X, s), (:X, s2), (:B1, unit(i, -u, -u)), (:B2, unit(i, -u, u))]
    global mixed_ok &= reduce((a, b) -> a .+ b, [c for (f, c) in mon]) == (0, 0, 0, 0, 0, 0)
    global mixed_ok &= count(x -> holo(x[2]), mon) == 2
    push!(mixed, (i, u, wvec(mon) .- 2 .* tau0))
end
check("B: 24 mixed quadruples (two X-characters, one of B_1, one of B_2), each of weight 0 and type (2,2)",
      mixed_ok && length(mixed) == 24)
const WT = [vcat(collect(c), 1) for (f, c) in ALL]        # 20 x 7
const rkMT = length(smith_invariants(WT, 7))
check("B: rank of Z^20 -> X^*(MT) is 7, so rank Lambda_H0 = 13", rkMT == 7 && 20 - rkMT == 13)
inH0(g) = all(sum(g[k] * WT[k][j] for k in 1:20) == 0 for j in 1:7)
function report(name, gens, rk)
    inv = smith_invariants(gens, 20)
    check("B: $name: rank $rk, all invariant factors 1 (and inside Lambda_H0)",
          all(inH0, gens) && length(inv) == rk && all(==(1), inv))
    inv
end
const L1 = vcat(pairs, [weilq])
const invL1 = report("Lambda_1 = <pairs, Weil quadruple of (X,k*)>", L1, 10)
report("<pairs> only", pairs, 9)
const invPM = report("<pairs, all 24 mixed quadruples>", vcat(pairs, [m[3] for m in mixed]), 13)
report("Lambda_1 + one mixed quadruple", vcat(L1, [mixed[1][3]]), 11)
report("Lambda_1 + mixed quadruples with i = 0", vcat(L1, [m[3] for m in mixed if m[1] == 0]), 11)
report("Lambda_1 + all mixed quadruples", vcat(L1, [m[3] for m in mixed]), 13)
in_L1(v) = smith_invariants(vcat(L1, [v]), 20) == invL1
let rep = Dict{Tuple{Int,Int},Vector{Int}}(), ok = true
    for (i, u, v) in mixed
        if haskey(rep, (i, u))
            ok &= in_L1(v .- rep[(i, u)])
        else
            rep[(i, u)] = v
        end
    end
    check("B: mod Lambda_1 the class q_(i,u) of a mixed quadruple depends only on (i,u)", ok)
    check("B: q_(i,-u) = -q_(i,u) mod Lambda_1", all(in_L1(rep[(i, 1)] .+ rep[(i, -1)]) for i in 0:2))
    check("B: a mixed quadruple is not in Lambda_1", !in_L1(rep[(0, 1)]))
end
check("B: the Weil quadruple of X lies in <pairs, mixed quadruples> = Lambda_H0 (index 1)",
      smith_invariants(vcat(pairs, [m[3] for m in mixed], [weilq]), 20) == invPM && length(invPM) == 13)

# ---------------------------------------------------------------- Part C
"subsets of the variables of X^nX x B_1 x B_2: by degree, #(Hodge) and #(in R_1)"
function count_classes(nX)
    variables = NTuple{9,Int}[]
    for k in 1:nX, c in Xch
        push!(variables, (c[1], c[2], c[3], 0, 0, 0, 0, 0, 0))
    end
    for c in B1ch
        i = findfirst(x -> abs(x) == 1, c[1:3]); w = zeros(Int, 9); w[3+i] = c[3+i]; push!(variables, Tuple(w))
    end
    for c in B2ch
        i = findfirst(x -> abs(x) == 1, c[1:3]); w = zeros(Int, 9); w[6+i] = c[3+i]; push!(variables, Tuple(w))
    end
    state = Dict{Tuple{NTuple{9,Int},Int},Int}((ntuple(_ -> 0, 9), 0) => 1)
    for v in variables
        new = copy(state)
        for ((w, d), m) in state
            key = (w .+ v, d + 1)
            new[key] = get(new, key, 0) + m
        end
        state = new
    end
    H = Dict{Int,Int}(); R = Dict{Int,Int}()
    for ((w, d), m) in state
        lam = ntuple(i -> w[i] + w[3+i] - w[6+i], 3); chi = ntuple(i -> w[3+i] + w[6+i], 3)
        if iseven(d) && lam == (0, 0, 0) && chi == (0, 0, 0)
            H[d] = get(H, d, 0) + m
            all(iszero, w) && (R[d] = get(R, d, 0) + m)
        end
    end
    H, R
end
symm(v) = vcat(v, reverse(v[1:end-1]))
let
    H, R = count_classes(1)
    ds = 0:2:20
    check("C: X x B_1 x B_2: dim of Hodge classes by degree 1,10,59,216,468,612,468,...",
          [get(H, d, 0) for d in ds] == symm([1, 10, 59, 216, 468, 612]))
    check("C: X x B_1 x B_2: dim of R_1 by degree 1,10,47,132,240,292,240,...",
          [get(R, d, 0) for d in ds] == symm([1, 10, 47, 132, 240, 292]))
    check("C: X x B_1 x B_2: open by degree 0,0,12,84,228,320,...; total 968",
          [get(H, d, 0) - get(R, d, 0) for d in ds] == symm([0, 0, 12, 84, 228, 320]) &&
          sum(values(H)) - sum(values(R)) == 968)
    H, R = count_classes(2)
    ds = 0:2:28
    check("C: X^2 x B_1 x B_2: dim of Hodge classes by degree 1,22,291,2204,10171,29942,57065,70800,...",
          [get(H, d, 0) for d in ds] == symm([1, 22, 291, 2204, 10171, 29942, 57065, 70800]))
    check("C: X^2 x B_1 x B_2: dim of R_1 by degree 1,22,243,1484,5555,13686,23161,27536,...",
          [get(R, d, 0) for d in ds] == symm([1, 22, 243, 1484, 5555, 13686, 23161, 27536]))
    check("C: X^2 x B_1 x B_2: open by degree 0,0,48,720,4616,16256,33904,43264,...; total 154352",
          [get(H, d, 0) - get(R, d, 0) for d in ds] == symm([0, 0, 48, 720, 4616, 16256, 33904, 43264]) &&
          sum(values(H)) - sum(values(R)) == 154352)
end

# ---------------------------------------------------------------- Part D
function mulg(g::GE, h::GE)::GE        # (g*h)(x) = g(h(x))
    p, e = g; q, f = h
    r = ntuple(j -> p[q[j]+1], 3)
    ee = zeros(Int, 3)
    for j in 1:3
        ee[p[q[j]+1]+1] = e[p[q[j]+1]+1] * f[q[j]+1]
    end
    (r, Tuple(ee))
end
const IDG = ((0, 1, 2), (1, 1, 1))
const CHIS = [("e_2 = 1 (E = K.K_2)", g -> g[2][2]), ("e_3 = 1 (E = K.K_3)", g -> g[2][3]),
              ("e_2 e_3 = 1 (E = K.k*)", g -> g[2][2] * g[2][3])]
for (nm, P, nfields, expgood) in (("A3", A3, 3, [0, 0, 4]), ("S3", S3, 1, [4]))
    G = gal(P)
    check("D: P = $nm: the composition law is compatible with the action on characters",
          all(act(mulg(g, h), c) == act(g, act(h, c)) for g in G for h in G for c in vcat(Xch, B1ch, B2ch)))
    P1 = [g for g in G if g[2] == (1, 1, 1) && g[1][1] == 0]          # Gal(Ktilde/N)
    StK = [g for g in G if g[1][1] == 0 && g[2][1] == 1]              # fixes tau_1
    check("D: P = $nm: [N:Q] = 24 and [K:Q] = 6", length(G) ÷ length(P1) == 24 && length(G) ÷ length(StK) == 6)
    ginv(g) = first(k for k in G if mulg(k, g) == IDG)
    results = Tuple{String,Bool,Int,Int,Int,Bool}[]
    for (cname, chi) in CHIS
        H = [g for g in StK if chi(g) == 1]
        (2 * length(H) == length(StK) && all(mulg(a, b) in H for a in H for b in H) && all(p in H for p in P1)) || continue
        Hs = Set(H)
        cm = !((((0, 1, 2), (-1, -1, -1))) in Hs)
        Nrm = [g for g in G if all(mulg(mulg(g, h), ginv(g)) in Hs for h in H)]
        cos(g) = sort([mulg(g, h) for h in H])
        embE = sort(unique([cos(g) for g in G]))
        auts = sort(unique([cos(a) for a in Nrm]))
        cosN(g) = sort([mulg(g, h) for h in P1])
        e1 = (1, 0, 0, 0, 0, 0)
        Phi1 = [(1, 0, 0), (0, 1, 0), (0, 0, 1)]; Phi2 = [(1, 0, 0), (0, 1, 0), (0, 0, -1)]
        good = 0; consistent = length(embE) == 12
        for a1 in auts, a2 in auts
            ra1 = first(a1); ra2 = first(a2)
            ok = true; chars_ok = true
            for sg in embE
                g = first(sg)
                above = unique([cosN(mulg(g, h)) for h in H])
                consistent &= length(above) == 2
                xs = [act(first(nu), (1, 1, 1, 0, 0, 0)) for nu in above]
                n10 = count(holo, xs)
                t1 = act(mulg(g, ra1), e1)[1:3]; t2 = act(mulg(g, ra2), e1)[1:3]
                n10 += (t1 in Phi1) + (t2 in Phi2)
                n10 != 2 && (ok = false)
                i = findfirst(x -> abs(x) == 1, t1); c1 = unit(i - 1, t1[i], t1[i])
                i = findfirst(x -> abs(x) == 1, t2); c2 = unit(i - 1, -t2[i], t2[i])
                reduce((a, b) -> a .+ b, [xs[1], xs[2], c1, c2]) == (0, 0, 0, 0, 0, 0) || (chars_ok = false)
            end
            consistent &= ok == chars_ok
            ok && (good += 1)
        end
        push!(results, (cname, cm, length(auts), good, length(auts)^2, consistent))
    end
    check("D: P = $nm: $nfields field(s) E of degree 12 with K in E in K.K*", length(results) == nfields)
    for (k, (cname, cm, na, good, tot, consistent)) in enumerate(results)
        check("D: P = $nm, H: $cname: CM field, |Aut(E)| = 4, Weil type (2,2) at all 12 places for $(expgood[k]) of 16 twists " *
              "(Weil type <=> the four characters sum to 0 at every place)",
              cm && na == 4 && tot == 16 && good == expgood[k] && consistent)
    end
end

# ================================================================ Part 2
setprecision(BigFloat, 256)
is_square(n::Integer) = n >= 0 && isqrt(n)^2 == n
function legendre(a, p)
    a = mod(a, p)
    a == 0 && return 0
    powermod(a, (p - 1) ÷ 2, p) == 1 ? 1 : -1
end
"Hilbert symbol (a,b)_p for nonzero integers, p prime or p = 0 for the real place"
function hilbert(a::BigInt, b::BigInt, p::BigInt)
    p == 0 && return (a < 0 && b < 0) ? -1 : 1
    al = 0
    while a % p == 0
        a ÷= p; al += 1
    end
    be = 0
    while b % p == 0
        b ÷= p; be += 1
    end
    if p == 2
        eps(u) = mod((u - 1) ÷ 2, 2)
        om(u) = mod((u * u - 1) ÷ 8, 2)
        return iseven(eps(a) * eps(b) + al * om(b) + be * om(a)) ? 1 : -1
    end
    r = iseven(al * be * ((p - 1) ÷ 2)) ? 1 : -1
    isodd(be) && (r *= legendre(a, p))
    isodd(al) && (r *= legendre(b, p))
    r
end
"deterministic Miller-Rabin (bases 2..41, valid below 3.3e24)"
function isprime_mr(n::BigInt)
    n < 2 && return false
    bases = BigInt[2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41]
    for q in bases
        n == q && return true
        n % q == 0 && return false
    end
    n < big(10)^24 || error("isprime_mr: out of range")
    d = n - 1; s = 0
    while iseven(d)
        d ÷= 2; s += 1
    end
    for a in bases
        x = powermod(a, d, n)
        (x == 1 || x == n - 1) && continue
        comp = true
        for _ in 1:s-1
            x = powermod(x, 2, n)
            if x == n - 1
                comp = false; break
            end
        end
        comp && return false
    end
    true
end
"a nontrivial factor of the composite n (Pollard rho, deterministic)"
function rho(n::BigInt)
    c = big(1)
    while true
        x = big(2); y = big(2); d = big(1)
        while d == 1
            x = mod(x * x + c, n)
            y = mod(y * y + c, n); y = mod(y * y + c, n)
            d = gcd(abs(x - y), n)
        end
        d != n && return d
        c += 1
    end
end
function primes_of(n::BigInt)
    n = abs(n); ps = Set{BigInt}()
    for d in 2:2000
        if n % d == 0
            push!(ps, big(d))
            while n % d == 0
                n ÷= d
            end
        end
    end
    stack = n > 1 ? [n] : BigInt[]
    while !isempty(stack)
        m = pop!(stack)
        if isprime_mr(m)
            push!(ps, m)
        elseif is_square(m)
            push!(stack, isqrt(m))
        else
            d = rho(m); push!(stack, d); push!(stack, m ÷ d)
        end
    end
    ps
end
"is the integer m != 0 a norm from Q(sqrt(D))?  (Hasse norm theorem: all Hilbert symbols (m, D)_v = 1)"
is_norm_from(m::BigInt, D::BigInt) =
    all(hilbert(m, D, p) == 1 for p in vcat(sort(collect(union(primes_of(m), primes_of(D), Set([big(2)])))), [big(0)]))
function squarefree_part(n::Integer)
    s = n > 0 ? 1 : -1; n = abs(n); d = 2
    while d * d <= n
        k = 0
        while n % d == 0
            n ÷= d; k += 1
        end
        isodd(k) && (s *= d)
        d += 1
    end
    s * n
end
function det_exact(M0)
    M = Rational{BigInt}.(M0); n = size(M, 1); d = one(Rational{BigInt})
    for c in 1:n
        piv = findfirst(i -> M[i, c] != 0, c:n)
        piv === nothing && return zero(Rational{BigInt})
        piv += c - 1
        if piv != c
            M[[c, piv], :] = M[[piv, c], :]; d = -d
        end
        d *= M[c, c]
        for i in c+1:n
            f = M[i, c] / M[c, c]
            M[i, :] .-= f .* M[c, :]
        end
    end
    d
end
"discriminant of a monic polynomial g (coefficients from the leading one) as (-1)^(n(n-1)/2) Res(g, g')"
function disc_monic(g)
    n = length(g) - 1
    dg = [g[i] * (n - i + 1) for i in 1:n]
    S = zeros(BigInt, 2n - 1, 2n - 1)
    for i in 1:n-1, j in 1:n+1
        S[i, i+j-1] = g[j]
    end
    for i in 1:n, j in 1:n
        S[n-1+i, i+j-1] = dg[j]
    end
    r = det_exact(S)
    numerator(iseven(n * (n - 1) ÷ 2) ? r : -r)
end
"the three real roots of the monic cubic x^3 + c[3] x^2 + c[2] x + c[1], ascending, in BigFloat"
function real_roots_cubic(c)
    f(x) = ((x + c[3]) * x + c[2]) * x + c[1]
    roots = BigFloat[]
    for k in 0:19999
        a = -10 + big(k) // 1000; b = a + 1 // big(1000)
        fa = f(a); fb = f(b)
        fa == 0 && error("rational root")
        if fa * fb < 0
            lo = BigFloat(a); hi = BigFloat(b); slo = sign(fa)
            for _ in 1:300
                mid = (lo + hi) / 2
                sign(f(mid)) == slo ? (lo = mid) : (hi = mid)
            end
            push!(roots, (lo + hi) / 2)
        end
    end
    roots
end
polmulmod(a, b, p) = begin                 # ascending coefficient vectors mod p
    r = zeros(Int, length(a) + length(b) - 1)
    for i in eachindex(a), j in eachindex(b)
        r[i+j-1] = mod(r[i+j-1] + a[i] * b[j], p)
    end
    r
end

const CLASSES = [(1, 1, 1), (1, -1, -1), (-1, 1, -1), (-1, -1, 1)]     # embeddings of K*+ : e up to sign

function run_field(name, cubic, shift, dF, expected)
    c0, c1, c2 = cubic                                   # eta^3 + c2 eta^2 + c1 eta + c0 = 0
    # elementary symmetric functions of eta and of delta = shift + eta (exact)
    s1 = -c2; s2 = c1; s3 = -c0
    E1 = 3shift + s1; E2 = 3shift^2 + 2shift * s1 + s2; E3 = shift^3 + shift^2 * s1 + shift * s2 + s3
    discF = disc_monic(BigInt[1, c2, c1, c0])
    check("$name: disc(x^3 + ($c2)x^2 + ($c1)x + ($c0)) = d_F = $dF > 0 (F totally real)", discF == dF)
    Nd = E3
    Dk = squarefree_part(-Nd)
    check("$name: delta = $shift + eta is totally positive (e_1, e_2, e_3 > 0), N(delta) = $(expected.Nd), k* = Q(sqrt($(expected.Dk)))",
          E1 > 0 && E2 > 0 && E3 > 0 && Nd == expected.Nd && Dk == expected.Dk)
    # delta not in Q^x F^x2: if delta = d g^2 then delta N(delta) is a square in F.  Certificate: a prime p and a
    # simple root r of the minimal polynomial h of u = delta N(delta) mod p (a prime of degree 1 of F) with r a non-residue.
    # h(x) = x^3 - Nd E1 x^2 + Nd^2 E2 x - Nd^3 E3
    hc = BigInt[-big(Nd)^3 * E3, big(Nd)^2 * E2, -big(Nd) * E1, 1]
    cert = nothing
    for p in 3:2:200
        all(p % q != 0 for q in 2:isqrt(p)) || continue
        for r in 1:p-1
            hv = mod(((r + hc[3]) * r + hc[2]) * r + hc[1], p)
            hd = mod(3r^2 + 2hc[3] * r + hc[2], p)
            if hv == 0 && hd != 0 && legendre(r, p) == -1
                cert = (p, r); break
            end
        end
        cert === nothing || break
    end
    check("$name: delta is not in Q^x F^x2, so K has no imaginary quadratic subfield (certificate (p, r) = $cert)", cert !== nothing)
    # reflex field: theta = sum e_i sqrt(-delta_i), b = theta^2 + E1 = -2 sum_{i<j} e_i e_j sqrt(delta_i delta_j);
    # the four conjugates are -2(+-q1 +- q2 +- q3) with an even number of minus signs, so
    # g(x) = x^4 - 8 E2 x^2 + 64 E3 x + 16 (E2^2 - 4 E1 E3)
    shiftb = -E1
    g = BigInt[1, 0, -8 * E2, 64 * E3, 16 * (E2^2 - 4 * E1 * E3)]
    check("$name: K*+ = Q(b), b = theta^2 - ($(expected.shiftb)), minimal polynomial $(expected.g)",
          shiftb == expected.shiftb && g == expected.g)
    eta = real_roots_cubic(cubic)
    delta = [shift + r for r in eta]
    sq = sqrt.(delta)
    bval(e) = -sum(delta) - 2 * (e[1] * e[2] * sq[1] * sq[2] + e[1] * e[3] * sq[1] * sq[3] + e[2] * e[3] * sq[2] * sq[3])
    bs = [bval(e) - shiftb for e in CLASSES]
    geval(x) = (((x + g[2]) * x + g[3]) * x + g[4]) * x + g[5]
    check("$name: three real roots of the cubic and the four values b_e are roots of g (|g(b_e)| < 1e-60)",
          length(eta) == 3 && all(abs(geval(b)) < big"1e-60" for b in bs) &&
          all(abs(bs[i] - bs[j]) > 1e-3 for i in 1:4 for j in i+1:4))
    discg = disc_monic(g)
    check("$name: disc(g) = $(expected.discg) and disc(g)/d_F = $(expected.discg ÷ dF) is a rational square",
          discg == expected.discg && discg % dF == 0 && is_square(discg ÷ dF))
    # exact arithmetic in Z[x]/(g)
    mulx(v) = BigInt[-g[5] * v[4], v[1] - g[4] * v[4], v[2] - g[3] * v[4], v[3] - g[2] * v[4]]
    function polymul_mod(u, w)
        acc = zeros(BigInt, 4); cur = BigInt.(collect(w))
        for k in 1:4
            acc .+= u[k] .* cur; cur = mulx(cur)
        end
        acc
    end
    function norm(v)
        M = zeros(BigInt, 4, 4)
        for j in 1:4
            bv = zeros(BigInt, 4); bv[j] = 1
            M[:, j] = polymul_mod(v, bv)
        end
        numerator(det_exact(M))
    end
    cands = Set{NTuple{4,BigInt}}()
    for a in -4:4, b in -4:4, c in -4:4, d in -4:4
        (a, b, c, d) == (0, 0, 0, 0) || push!(cands, BigInt.((a, b, c, d)))
    end
    lo = Int(floor(minimum(bs))) - 3; hi = Int(ceil(maximum(bs))) + 3
    for k in 1:3
        rs = fill(lo, k)
        while true                                       # combinations with replacement of lo:hi
            v = BigInt[1, 0, 0, 0]
            for r in rs
                v = polymul_mod(v, BigInt[-r, 1, 0, 0])
            end
            push!(cands, Tuple(v))
            i = k
            while i >= 1 && rs[i] == hi
                i -= 1
            end
            i == 0 && break
            rs[i] += 1
            for j in i+1:k
                rs[j] = rs[i]
            end
        end
    end
    candlist = collect(cands)
    sgns = Vector{Vector{Int}}(undef, length(candlist)); minabs = big(1.0)
    for (k, c) in enumerate(candlist)
        vals = [c[1] + c[2] * r + c[3] * r^2 + c[4] * r^3 for r in bs]
        minabs = min(minabs, minimum(abs.(vals)))
        sgns[k] = [v > 0 ? 1 : -1 for v in vals]
    end
    check("$name: no candidate vanishes at a real place within 1e-9 (signs are well determined)", minabs > 1e-9)
    normcache = Dict{Int,Tuple{BigInt,Bool}}()
    for split in 0:2
        o = [i for i in 0:2 if i != split]
        want = [(e[o[1]+1] * e[split+1]) * (e[o[2]+1] * e[split+1]) for e in CLASSES]
        hits = Tuple{BigInt,NTuple{4,BigInt},NTuple{4,BigInt}}[]; tested = 0; allpos = true
        for (k, c) in enumerate(candlist)
            (sgns[k] == want || sgns[k] == -want) || continue
            tested += 1
            n, isn = get!(normcache, k) do
                n = norm(c)
                (n, n > 0 && is_norm_from(n * dF, big(Dk)))
            end
            allpos &= n > 0
            isn && push!(hits, (abs(n), abs.(c), c))
        end
        sort!(hits)
        ex = expected.splits[split+1]
        check("$name, split place $split: required signs $(ex.want); admissible a tested: $(ex.tested) (all of positive norm); " *
              "with N(a) d_F in Nm(k*): $(ex.hits)",
              want == ex.want && tested == ex.tested && allpos && length(hits) == ex.hits)
        n, _, c = hits[1]
        val = n * dF
        rep = nothing
        for z in 1:399
            t = val * z * z
            for y in 0:isqrt(t ÷ abs(Dk))
                r2 = t - abs(Dk) * y * y
                if is_square(r2)
                    rep = (isqrt(r2), big(y), big(z)); break
                end
            end
            rep === nothing || break
        end
        check("$name, split place $split: smallest example a = $(ex.a), N(a) = $(ex.n), N(a) d_F = $(ex.n * dF) = (x^2 + $(abs(Dk)) y^2)/z^2 " *
              "with (x,y,z) = $(ex.rep)",
              collect(c) == ex.a && n == ex.n && rep == ex.rep &&
              rep[1]^2 + abs(Dk) * rep[2]^2 == val * rep[3]^2)
    end
end

sp(want, tested, hits, a, n, rep) = (want=want, tested=tested, hits=hits, a=a, n=big(n), rep=big.(rep))
run_field("F = Q(zeta_7)^+", (-1, -2, 1), 3, 49,
          (Nd=13, Dk=-13, shiftb=-8, g=[1, 0, -152, 832, -880], discg=big(138932125696),
           splits=[sp([1, 1, -1, -1], 1806, 438, [-4, 1, 0, 0], 272, (100, 16, 1)),
                   sp([1, -1, 1, -1], 128, 11, [48, 4, -8, 1], 54591488, (51712, 256, 1)),
                   sp([1, -1, -1, 1], 288, 14, [-12, -4, 1, 0], 200704, (3136, 0, 1))]))
run_field("F = Q(zeta_9)^+", (1, -3, 0), 3, 81,
          (Nd=17, Dk=-17, shiftb=-9, g=[1, 0, -192, 1088, -576], discg=big(392737849344),
           splits=[sp([1, 1, -1, -1], 4057, 1429, [-7, 1, 0, 0], 33, (49, 4, 1)),
                   sp([1, -1, 1, -1], 119, 33, [0, 56, -15, 1], 1216512, (9408, 768, 1)),
                   sp([1, -1, -1, 1], 153, 30, [0, -8, 1, 0], 36864, (1728, 0, 1))]))
run_field("F = cubic field of discriminant 148", (1, -3, -1), 3, 148,
          (Nd=26, Dk=-26, shiftb=-10, g=[1, 0, -240, 1664, -2240], discg=big(1678526906368),
           splits=[sp([1, 1, -1, -1], 2268, 103, [-4, 1, 0, 0], 832, (1040, 32, 3)),
                   sp([1, -1, 1, -1], 240, 12, [504, -79, -6, 1], 283133760, (203216, 4832, 1)),
                   sp([1, -1, -1, 1], 360, 6, [-72, 1, 1, 0], 5778240, (11024, 5312, 1))]))

println("mumford_residual.jl: ", NPASS[], " checks passed, ", NFAIL[], " failed")
NFAIL[] > 0 && exit(1)
