# cm_sixfolds.jl -- the enumeration behind Theorem thm:cmkl: Hodge rings of
# abelian sixfolds with complex multiplication by a CM field M = K L of degree
# 12, K imaginary quadratic, L totally real sextic.  The Galois group of the
# Galois closure is Z/2 x Gamma, Gamma a transitive subgroup of S_6, acting on
# the twelve embeddings X = {+,-} x {1..6}.  A CM type is
# Phi_I = {(+,i) : i in I} u {(-,j) : j not in I}.  By Pohlmann's criterion the
# Hodge classes of degree 2p are spanned by the monomials e_S, |S| = 2p, with
# |g S cap Phi| = p for every g; products of divisor classes span the unions
# of disjoint Hodge monomials of degree 2; the Weil classes of an imaginary
# quadratic subfield K' are the e_S with S the set of embeddings restricting
# to one embedding of K'.  Every transitive subgroup of S_6 is enumerated as a
# closure <g, h> with all its conjugates (279 subgroups, 16 classes), so that
# I = {1..k} suffices.  Also the cyclotomic fields Q(zeta_m), m = 21, 28, 36.
# Run: julia --startup-file=no cm_sixfolds.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms: Checks, check, finish

const P6 = [Tuple(p) for p in Iterators.product(ntuple(_ -> 1:6, 6)...) if allunique(p)]
pmul(p, q) = ntuple(i -> p[q[i]], 6)
pinv(p) = (r = zeros(Int, 6); for i in 1:6; r[p[i]] = i; end; Tuple(r))
function ctype(p)
    seen = falses(6); t = Int[]
    for i in 1:6
        seen[i] && continue
        l = 0; j = i
        while !seen[j]; seen[j] = true; j = p[j]; l += 1; end
        push!(t, l)
    end
    return sort(t)
end
function closure(gens)
    G = Set([ntuple(identity, 6)]); fr = collect(G)
    while !isempty(fr)
        new = []
        for x in fr, g in gens
            y = pmul(g, x)
            y in G || (push!(G, y); push!(new, y))
        end
        fr = new
    end
    return G
end
transitive(G) = length(Set(g[1] for g in G)) == 6

bit(s, i) = 1 << (6s + i - 1)                 # s = 0 for +, 1 for -
const SUBS = Dict(k => [m for m in 0:4095 if count_ones(m) == k] for k in (2, 4, 6, 8, 10))

"Hodge monomials B[p], divisor monomials D[p] (p = 1..5) for the CM types conj"
function hodge(conj)
    B = Dict(p => Set(m for m in SUBS[2p] if all(count_ones(m & P) == p for P in conj)) for p in 1:5)
    D = Dict(1 => copy(B[1]))
    for p in 2:5
        D[p] = Set(S | T for S in D[p-1] for T in B[1] if S & T == 0)
    end
    return B, D
end

function main()
    C = Checks("cm_sixfolds.jl")
    reps = Dict{Vector{Int},Any}()
    for p in P6; get!(reps, ctype(p), p); end
    subs = Set{Set{NTuple{6,Int}}}()
    for g in values(reps), h in P6
        H = closure([g, h]); transitive(H) && push!(subs, H)
    end
    allsubs = Set{Set{NTuple{6,Int}}}()
    for H in subs, s in P6
        si = pinv(s); push!(allsubs, Set(pmul(pmul(s, h), si) for h in H))
    end
    classes = Set{Any}()
    for H in allsubs
        push!(classes, (length(H), sort([(k, v) for (k, v) in countmap(ctype.(collect(H)))])))
    end
    check(C, "transitive subgroups of S_6: $(length(allsubs)) (expected 279) in $(length(classes)) classes by order and cycle statistics (expected 16)",
          length(allsubs) == 279 && length(classes) == 16)
    ok = true; ncases = 0; weilneeded = 0; s6data = Dict()
    for H in allsubs, k in 0:6
        I = 1:k
        Phi = sum(bit(0, i) for i in I; init = 0) + sum(bit(1, j) for j in 1:6 if !(j in I); init = 0)
        conj = Set{Int}()
        for p in H
            P = 0
            for s in 0:1, i in 1:6
                (Phi & bit(s, i)) != 0 && (P |= bit(s, p[i]))
            end
            push!(conj, P); push!(conj, ((P & 63) << 6) | (P >> 6))
        end
        B, D = hodge(conj)
        W = Set{Int}()
        k == 3 && union!(W, [63, 63 << 6])
        for T in Iterators.filter(t -> 1 in t, [findall(==(1), digits(m, base = 2, pad = 6)) for m in 0:63 if count_ones(m) == 3])
            Tc = setdiff(1:6, T)
            all(Set(p[i] for i in T) in (Set(T), Set(Tc)) for p in H) || continue
            S0 = sum(bit(0, i) for i in T) + sum(bit(1, i) for i in Tc)
            S1 = ((S0 & 63) << 6) | (S0 >> 6)
            all(count_ones(S0 & P) == 3 for P in conj) && union!(W, [S0, S1])
        end
        ok &= B[2] == D[2] && issubset(setdiff(B[3], D[3]), W) && B[4] == D[4] && B[5] == D[5] && B[1] == D[1]
        !isempty(setdiff(W, D[3])) && (weilneeded += 1)
        ncases += 1
        if length(H) in (720, 360)
            s6data[(length(H), k)] = [length(B[p]) for p in 1:5]
        end
    end
    check(C, "all $ncases pairs (Gamma, |I|): B^2 = D^2, B^4 = D^4, B^5 = D^5, and B^3 is spanned by D^3 and the Weil classes of the imaginary quadratic subfields",
          ok && ncases == 279 * 7)
    check(C, "the Weil classes are needed (not in D^3) in $weilneeded of the $ncases cases", weilneeded > 0)
    want = Dict(0 => [36, 225, 400, 225, 36], 1 => [6, 15, 20, 15, 6], 2 => [6, 15, 20, 15, 6], 3 => [6, 15, 22, 15, 6],
                4 => [6, 15, 20, 15, 6], 5 => [6, 15, 20, 15, 6], 6 => [36, 225, 400, 225, 36])
    check(C, "Gamma = S_6 and A_6: dim B^p = 6,15,20,15,6 for |I| != 0,3,6; 6,15,22,15,6 for |I| = 3; 36,225,400,225,36 for I empty or full",
          all(s6data[(o, k)] == want[k] for o in (720, 360) for k in 0:6))

    # cyclotomic fields
    for m in (21, 28, 36)
        G = [a for a in 1:m-1 if gcd(a, m) == 1]
        idx = Dict(a => i for (i, a) in enumerate(G))
        reps2 = [a for a in G if a < m - a]
        subsK = [H for H in Iterators.filter(S -> length(S) == 6, [Set(G[findall(==(1), digits(x, base = 2, pad = 12))]) for x in 0:4095 if count_ones(x) == 6])
                 if 1 in H && !(m - 1 in H) && all(mod(a * b, m) in H for a in H for b in H)]
        weil = Set{Int}()
        for H in subsK
            mH = sum(1 << (idx[a] - 1) for a in H); push!(weil, mH, 4095 ⊻ mH)
        end
        ndiv = 0; nweil = 0; nother = 0; orbits = Set{Any}()
        for x in 0:63
            Phi = Set(((x >> (i - 1)) & 1 == 1 ? a : m - a) for (i, a) in enumerate(reps2))
            conj = Set(sum(1 << (idx[mod(g * a, m)] - 1) for a in Phi) for g in G)
            B, D = hodge(conj)
            if all(B[p] == D[p] for p in 1:5)
                ndiv += 1
            elseif all(B[p] == D[p] for p in (1, 2, 4, 5)) && issubset(setdiff(B[3], D[3]), weil) && length(setdiff(B[3], D[3])) == 2
                nweil += 1; push!(orbits, conj)
            else
                nother += 1
            end
        end
        check(C, "Q(zeta_$m): $(length(subsK)) imaginary quadratic subfields; of the 64 CM types $ndiv divisor-generated, $nweil need exactly two Weil classes ($(length(orbits)) orbits of 12), $nother other",
              ndiv == 40 && nweil == 24 && nother == 0 && length(orbits) == 2)
    end
    finish(C)
end
countmap(v) = (d = Dict{eltype(v),Int}(); for x in v; d[x] = get(d, x, 0) + 1; end; d)
main()
