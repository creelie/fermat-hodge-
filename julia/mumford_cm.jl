# mumford_cm.jl -- port of the round programs r1-MUM/mum_checks.py and
# r1-MUM/mum_checks2.py: the link class xi of a Mumford fourfold X at CM points.
#
# Part 1  G x K^1 = SL_2^3 x T^3 invariants of degree 4 on X x X x Z_K by Kuenneth
#         type (26 in all), and dim (wedge^k V)^G for k = 2, 4, 6, from characters.
# Part 2  Pohlmann's criterion at CM points: the Hodge monomials in
#         H^1(X) (x) H^1(X) (x) wedge^2 H^1(Z_K) for six Galois configurations of
#         (L, K), which of them are products of divisor monomials, the rest.
# Part 3  Theorem A, Step 1, by brute force: on E^a x A^b every Hodge monomial has
#         d_1 = d_2 = d_3 = d_E (it is a product of conjugate pairs and Weil
#         quadruples), for the Galois groups P = A3 and S3.
# Part 4  (mum_checks2.py) X_t ~ E x A for L = F.k': Hodge monomials on X_t and on
#         X_t x X_t in Kuenneth type (2,2), and those not products of divisor monomials.
# Integer arithmetic only.
# Run: julia --startup-file=no mumford_cm.jl

const NPASS = Ref(0); const NFAIL = Ref(0)
function check(name, ok)
    ok ? (NPASS[] += 1) : (NFAIL[] += 1)
    println(ok ? "PASS " : "FAIL ", name)
end
const Ch = NTuple{6,Int}
dot6(a, b) = sum(a .* b)
"all k-subsets of 1:n, in lexicographic order"
function combinations(n, k)
    out = Vector{Int}[]; c = collect(1:k)
    k > n && return out
    while true
        push!(out, copy(c))
        i = k
        while i >= 1 && c[i] == n - k + i
            i -= 1
        end
        i == 0 && break
        c[i] += 1
        for j in i+1:k
            c[j] = c[j-1] + 1
        end
    end
    out
end

# ---------------------------------------------------------------- Part 1
function wedge_char(ws, k)
    res = Dict{Ch,Int}()
    k == 0 && (res[(0, 0, 0, 0, 0, 0)] = 1; return res)
    for comb in combinations(length(ws), k)
        w = reduce((a, b) -> a .+ b, ws[comb])
        res[w] = get(res, w, 0) + 1
    end
    res
end
function mulchar(c1, c2)
    r = Dict{Ch,Int}()
    for (w1, m1) in c1, (w2, m2) in c2
        r[w1.+w2] = get(r, w1 .+ w2, 0) + m1 * m2
    end
    r
end
"dimension of the SL_2^3 x T^3 invariants; weights are (g1, g2, g3, t1, t2, t3)"
inv_dim(ch) = sum((-1)^(a + b + c) * get(ch, (2a, 2b, 2c, 0, 0, 0), 0) for a in 0:1, b in 0:1, c in 0:1)
const Vw = Ch[(a, b, c, 0, 0, 0) for a in (1, -1) for b in (1, -1) for c in (1, -1)]
const Dw = Ch[ntuple(j -> j == i ? u : j == 3 + i ? v : 0, 6) for i in 1:3 for u in (1, -1) for v in (1, -1)]
println("== Part 1: invariants of G.K^1 = SL2^3 x T^3 ==")
d2, d4, d6 = inv_dim(wedge_char(Vw, 2)), inv_dim(wedge_char(Vw, 4)), inv_dim(wedge_char(Vw, 6))
check("dim (wedge^2 V)^G = $d2 = 1, dim (wedge^4 V)^G = $d4 = 1, dim (wedge^6 V)^G = $d6 = 1", (d2, d4, d6) == (1, 1, 1))
dvv = inv_dim(mulchar(wedge_char(Vw, 1), wedge_char(Vw, 1)))
dd2, dd4 = inv_dim(wedge_char(Dw, 2)), inv_dim(wedge_char(Dw, 4))
check("dim (V (x) V)^G = $dvv = 1, dim (wedge^2 D)^{G K^1} = $dd2 = 3, dim (wedge^4 D)^{G K^1} = $dd4 = 6", (dvv, dd2, dd4) == (1, 3, 6))
kdims = [(a, b, 4 - a - b) => inv_dim(mulchar(mulchar(wedge_char(Vw, a), wedge_char(Vw, b)), wedge_char(Dw, 4 - a - b)))
         for a in 0:4 for b in 0:4-a]
for (ty, d) in kdims
    d > 0 && println("  Kuenneth type $ty dim $d")
end
tot = sum(d for (_, d) in kdims)
check("total number of degree-4 invariants on X x X x Z_K: $tot = 26", tot == 26)
check("Kuenneth breakdown (0,0,4) 6, (0,2,2) 3, (0,4,0) 1, (1,1,2) 6, (1,3,0) 1, (2,0,2) 3, (2,2,0) 4, (3,1,0) 1, (4,0,0) 1",
      [p for p in kdims if p.second > 0] == [(0, 0, 4) => 6, (0, 2, 2) => 3, (0, 4, 0) => 1, (1, 1, 2) => 6, (1, 3, 0) => 1,
                                             (2, 0, 2) => 3, (2, 2, 0) => 4, (3, 1, 0) => 1, (4, 0, 0) => 1])
d22 = inv_dim(mulchar(wedge_char(Vw, 2), wedge_char(Vw, 2)))
check("Kuenneth type (2,2,0): dim $d22 = 4 (= Q + F)", d22 == 4)

# ---------------------------------------------------------------- Part 2
println("== Part 2: CM points, Pohlmann criterion ==")
const MU = (0, 0, 1, 1, 1, 0)      # Hodge cocharacter (times 2) in X_*(L^1 x K^1); holomorphic iff the pairing is > 0
const Xch = Vw; const Zch = Dw
check("every character of X_t and Z_t pairs to +-1 with the Hodge cocharacter", all(abs(dot6(c, MU)) == 1 for c in vcat(Xch, Zch)))
const A3 = [[1, 2, 3], [2, 3, 1], [3, 1, 2]]
const S3 = [[1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]]
# signed permutations of Z^3 + Z^3: the permutation on both triples, the sign vector (eL, eK)
act(g, ch) = (p = g[1]; s = g[2]; ntuple(j -> j <= 3 ? s[j] * ch[p[j]] : s[j] * ch[3+p[j-3]], 6))
function closure(gens)
    S = Set{Ch}(gens)
    while true
        new = setdiff(Set(x .* y for x in S for y in S), S)
        isempty(new) && return sort(collect(S))
        union!(S, new)
    end
end
const one6 = (1, 1, 1, 1, 1, 1)
const allsign3 = [(a, b, c) for a in (1, -1) for b in (1, -1) for c in (1, -1)]
cat3(e, f) = (e..., f...)
const cases = [
    ("1: L=K=F.k (k imag. quadratic)", closure([one6, (-1, -1, -1, -1, -1, -1)])),
    ("2: L=F.k', K=F.k, k!=k'", closure([one6, (-1, -1, -1, 1, 1, 1), (1, 1, 1, -1, -1, -1)])),
    ("3: L=K, no imag. quadratic subfield", closure(vcat([one6], [cat3(e, e) for e in allsign3]))),
    ("4: L=F.k', K generic", closure(vcat([one6, (-1, -1, -1, 1, 1, 1)], [cat3((1, 1, 1), e) for e in allsign3]))),
    ("5: L generic, K=F.k", closure(vcat([one6, (1, 1, 1, -1, -1, -1)], [cat3(e, (1, 1, 1)) for e in allsign3]))),
    ("6: L, K generic, linearly disjoint over F", closure(vcat([one6], [cat3(e, (1, 1, 1)) for e in allsign3], [cat3((1, 1, 1), e) for e in allsign3])))]
function rank6(vectors)
    M = [Rational{Int}.(collect(v)) for v in vectors]; r = 0
    for c in 1:6
        piv = findfirst(i -> M[i][c] != 0, r+1:length(M))
        piv === nothing && continue
        piv += r
        M[r+1], M[piv] = M[piv], M[r+1]
        for i in eachindex(M)
            if i != r + 1 && M[i][c] != 0
                M[i] = M[i] .- (M[i][c] / M[r+1][c]) .* M[r+1]
            end
        end
        r += 1
    end
    r
end
# expected: |Gal image|, rank, #chars of X, orbits of X, #chars of Z, multiplicities, orbits of Z, common, Hodge, products, others, not products in supp
const EXPECT2 = [
    (6, 3, 8, [2, 6], 8, [1, 1, 1, 1, 1, 1, 3, 3], [2, 6], 8, 246, 198, 48, 12),
    (12, 6, 8, [2, 6], 12, fill(1, 12), [12], 0, 72, 48, 24, 24),
    (24, 6, 8, [8], 12, fill(1, 12), [6, 6], 0, 72, 48, 24, 24),
    (48, 6, 8, [2, 6], 12, fill(1, 12), [12], 0, 72, 48, 24, 24),
    (48, 6, 8, [8], 12, fill(1, 12), [12], 0, 72, 48, 24, 24),
    (192, 6, 8, [8], 12, fill(1, 12), [12], 0, 72, 48, 24, 24)]
for (ci, (name, signs)) in enumerate(cases)
    G = [(p, s) for p in A3 for s in signs]
    conj_mu = sort(unique([act(g, MU) for g in G]))
    rk = rank6(conj_mu)
    # Pohlmann: a monomial is a Hodge class iff every Galois conjugate has type (p,p)
    is_hodge(mon) = all(count(ch -> dot6(ch, m) > 0, mon) == length(mon) ÷ 2 for m in conj_mu)
    restr(ch) = [dot6(ch, m) for m in conj_mu]
    xr = Dict{Vector{Int},Int}(); zr = Dict{Vector{Int},Int}()
    for c in Xch
        xr[restr(c)] = get(xr, restr(c), 0) + 1
    end
    for c in Zch
        zr[restr(c)] = get(zr, restr(c), 0) + 1
    end
    common = intersect(Set(keys(xr)), Set(keys(zr)))
    function orbits(chars)
        seen = Set{Vector{Int}}(); out = Int[]
        for c in chars
            restr(c) in seen && continue
            orb = Set(restr(act(g, c)) for g in G)
            union!(seen, orb); push!(out, length(orb))
        end
        sort(out)
    end
    pairh = Dict((u, v) => is_hodge((u, v)) for u in vcat(Xch, Zch) for v in vcat(Xch, Zch))
    hodge = NTuple{4,Ch}[]; dec = 0; nondec = NTuple{4,Ch}[]
    for s in Xch, s2 in Xch, i1 in 1:12, i2 in i1+1:12
        z1, z2 = Zch[i1], Zch[i2]
        mon = (s, s2, z1, z2)
        is_hodge(mon) || continue
        push!(hodge, mon)
        if (pairh[(s, s2)] && pairh[(z1, z2)]) || (pairh[(s, z1)] && pairh[(s2, z2)]) || (pairh[(s, z2)] && pairh[(s2, z1)])
            dec += 1
        else
            push!(nondec, mon)
        end
    end
    # support of xi^1: x_s x'_s' z_(-u e_i; f_i) z_(-u e_i; -f_i), s + s' = 2u e_i
    supp = NTuple{4,Ch}[]
    for i in 1:3, u in (1, -1), s in Xch
        s[i] == u || continue
        s2 = ntuple(j -> j > 3 ? 0 : j == i ? 2u - s[j] : -s[j], 6)
        z1 = ntuple(j -> j == i ? -u : j == 3 + i ? 1 : 0, 6); z2 = ntuple(j -> j == i ? -u : j == 3 + i ? -1 : 0, 6)
        push!(supp, (s, s2, z1, z2))
    end
    supp_hodge = all(is_hodge(m) for m in supp)
    nd = Set(nondec)
    k = count(m -> m in nd || (m[1], m[2], m[4], m[3]) in nd, supp)
    println("case $name")
    println("   |Gal image| = $(length(G)), rank of the Mumford-Tate torus (without weight) = $rk")
    println("   X_t: distinct characters on the MT torus $(length(xr)), Galois orbit sizes $(orbits(Xch)) | Z_t: distinct characters $(length(zr)),",
            " multiplicities $(sort(collect(values(zr)))), orbit sizes $(orbits(Zch))")
    println("   Hom(X_t, Z_t) != 0: $(!isempty(common)) (common characters: $(length(common)))")
    println("   Hodge monomials in H^1(X) (x) H^1(X) (x) wedge^2 H^1(Z): $(length(hodge)); products of two Hodge 2-monomials: $dec; others: $(length(nondec))")
    println("   support of xi^1: $(length(supp)) monomials, of which not products of divisor monomials: $k")
    ex = EXPECT2[ci]
    check("case $(name[1]): |Gal image| = $(ex[1]), Mumford-Tate torus of rank $(ex[2])", length(G) == ex[1] && rk == ex[2])
    check("case $(name[1]): X_t has $(ex[3]) characters in orbits $(ex[4]); Z_t has $(ex[5]) distinct characters, orbits $(ex[7]); common characters: $(ex[8])",
          length(xr) == ex[3] && orbits(Xch) == ex[4] && length(zr) == ex[5] && sort(collect(values(zr))) == ex[6] &&
          orbits(Zch) == ex[7] && length(common) == ex[8])
    check("case $(name[1]): $(ex[9]) Hodge monomials, $(ex[10]) products of divisor monomials, $(ex[11]) others",
          (length(hodge), dec, length(nondec)) == (ex[9], ex[10], ex[11]))
    check("case $(name[1]): the support of xi^1 is 24 Hodge monomials, $(ex[12]) of them not products of divisor monomials",
          length(supp) == 24 && supp_hodge && k == ex[12])
    if ci == 1
        ok = true
        for m in nondec
            rs = [restr(c) for c in m]
            ok &= all(==(0), sum(rs))
            ok &= !any(all(==(0), rs[a] + rs[b]) for a in 1:4 for b in a+1:4)
        end
        check("case 1: all 48 non-decomposable Hodge monomials are 4-term relations with no cancelling pair (Weil quadruples)", ok && length(nondec) == 48)
    else
        check("case $(name[1]): the non-decomposable Hodge monomials are exactly the support of xi^1 (up to the order of the z's)",
              Set(nondec) == Set((m[1], m[2], min(m[3], m[4]) == m[3] ? m[3] : m[4], min(m[3], m[4]) == m[3] ? m[4] : m[3]) for m in supp) ||
              Set(Set(m) for m in nondec) == Set(Set(m) for m in supp))
    end
end

# ---------------------------------------------------------------- Part 3
println("== Part 3: Theorem A, Step 1, brute force ==")
# embeddings of K = F.k: (i, e), e = +1 (restricts to iota on k) or -1; of k: e.
# Phi_A = {(1,-), (2,-), (3,+)}, Phi_E = {+}.  Galois: (permutation in A3 or S3, sign).
const PhiA = Set([(1, -1), (2, -1), (3, 1)])
"number of Hodge monomials of even degree <= maxdeg on E^a x A^b, and whether all have d_1 = d_2 = d_3 = d_E"
function checkA(a, b, maxdeg, perm_group)
    # variables: (isA, copy, i, e)
    vars = vcat([(true, c, i, e) for c in 1:b for i in 1:3 for e in (1, -1)], [(false, c, 0, e) for c in 1:a for e in (1, -1)])
    gal = [(p, s) for p in perm_group for s in (1, -1)]
    # holo[v, g]: is the conjugate of the variable v by g holomorphic
    holo = [(v[1] ? ((p[v[3]], s * v[4]) in PhiA) : (s * v[4] == 1)) for v in vars, (p, s) in gal]
    nH = 0; allok = true
    for dg in 2:2:maxdeg, mon in combinations(length(vars), dg)
        all(count(v -> holo[v, g], mon) == dg ÷ 2 for g in eachindex(gal)) || continue
        nH += 1
        d = [0, 0, 0, 0]                      # net signs: A-embeddings i = 1, 2, 3 and E
        for v in mon
            d[vars[v][1] ? vars[v][3] : 4] += vars[v][4]
        end
        allok &= d[1] == d[2] == d[3] == d[4]
    end
    nH, allok
end
const EXPECT3 = Dict((1, 1, 8) => 17, (2, 2, 6) => 580, (1, 3, 6) => 2353, (3, 2, 4) => 237, (5, 3, 4) => 1367)
for (a, b, md) in [(1, 1, 8), (2, 2, 6), (1, 3, 6), (3, 2, 4), (5, 3, 4)], (nm, grp) in (("A3", A3), ("S3", S3))
    n, ok = checkA(a, b, md, grp)
    check("E^$a x A^$b, degrees <= $md, P = $nm: $n = $(EXPECT3[(a, b, md)]) Hodge monomials, all with d_1 = d_2 = d_3 = d_E " *
          "(products of conjugate pairs and Weil quadruples)", ok && n == EXPECT3[(a, b, md)])
end

# ---------------------------------------------------------------- Part 4 (mum_checks2.py)
println("== Part 4: X_t ~ E x A for L = F.k' ==")
# characters of H^1(X_t) on the Mumford-Tate torus: sign vectors s, holomorphic iff s_3 = +1;
# Galois = (A3 or S3) x {+-1}
const S = [(a, b, c) for a in (1, -1) for b in (1, -1) for c in (1, -1)]
hodge2(mon) = all(count(s -> e * s[pi[3]] > 0, mon) == length(mon) ÷ 2 for pi in S3 for e in (1, -1))
function decomposable(mon::Vector)
    isempty(mon) && return true
    a = mon[1]
    for j in 2:length(mon)
        if all(==(0), a .+ mon[j]) && decomposable(vcat(mon[2:j-1], mon[j+1:end]))
            return true
        end
    end
    false
end
const quad = Set([(1, 1, -1), (1, -1, 1), (-1, 1, 1), (-1, -1, -1)])
for (dg, eH, end_) in ((2, 4, 0), (4, 8, 2))
    Hm = [S[c] for c in combinations(8, dg) if hodge2(S[c])]
    ndm = [m for m in Hm if !decomposable(m)]
    for m in ndm
        println("     ", m)
    end
    check("X_t, degree $dg: $(length(Hm)) = $eH Hodge monomials; not products of divisor monomials: $(length(ndm)) = $end_" *
          (dg == 4 ? " (the Weil quadruple and its conjugate)" : ""),
          length(Hm) == eH && length(ndm) == end_ && all(Set(m) == quad || Set(.-s for s in m) == quad for m in ndm))
end
H22 = Vector{NTuple{3,Int}}[]; nd22 = Vector{NTuple{3,Int}}[]
for c1 in combinations(8, 2), c2 in combinations(8, 2)
    mon = vcat(S[c1], S[c2])
    hodge2(mon) || continue
    push!(H22, mon)
    decomposable(mon) || push!(nd22, mon)
end
check("X_t x X_t, Kuenneth type (2,2): $(length(H22)) = 52 Hodge monomials; not products of divisor monomials: $(length(nd22)) = 12",
      length(H22) == 52 && length(nd22) == 12)
check("all the non-decomposable ones are the Weil quadruple or its conjugate",
      all(Set(m) == quad || Set(.-s for s in m) == quad for m in nd22))
check("the Weil quadruple has two characters of type (1,0) and two of type (0,1) (holomorphic iff s_3 = +1)",
      count(s -> s[3] > 0, quad) == 2 && count(s -> s[3] < 0, quad) == 2)

println("mumford_cm.jl: $(NPASS[]) checks passed, $(NFAIL[]) failed")
NFAIL[] > 0 && exit(1)
