# quadratic_forms.jl -- rational quadratic forms: Hilbert symbols, Hasse
# invariants and the classification of Hasse-Minkowski, in exact integer
# arithmetic (Base only).  Port of code/hilbert.c and of the symbol and
# classification parts of code/sqrt6_chain.py, kummer_type.py,
# fricke_lattice.py and of rounds/r1-F3/qf.py.
#
# A form is a vector of nonzero integers or rationals, the entries of a
# diagonalisation.  Conventions (Serre, A Course in Arithmetic, Ch. III, IV):
#   hilbert(a, b, p)   (a,b)_p, p a prime, or p = 0 for the real place;
#   hasse(q, p)        eps_p(<a_1..a_n>) = prod_{i<j} (a_i, a_j)_p;
#   disc(q)            the discriminant modulo squares, a squarefree integer.
# Two forms are isometric over Q iff they have the same rank, signature,
# discriminant and Hasse invariants at every prime (the invariants are 1
# outside 2 and the primes dividing a squarefree entry).
#
# Use:  include(joinpath(@__DIR__, "quadratic_forms.jl")); using .QuadraticForms
# Run alone (julia quadratic_forms.jl) it performs the checks of hilbert.c.
module QuadraticForms

export primes_of, sqfree, legendre, hilbert, disc, hasse, sig, relevant_primes,
       is_square_Qp, isometric, embeds, complement_data, scale, diagonalize,
       Checks, check, finish

"The primes dividing the nonzero integer n, in increasing order."
function primes_of(n::Integer)
    n = abs(n); ps = typeof(n)[]; p = oftype(n, 2)
    while p * p <= n
        if n % p == 0
            push!(ps, p)
            while n % p == 0; n = div(n, p); end
        end
        p += 1
    end
    n > 1 && push!(ps, n)
    return ps
end

"The squarefree integer s (sign kept) with x = s * (rational square)."
function sqfree(n::Integer)
    @assert n != 0
    s = n < 0 ? -one(n) : one(n); n = abs(n); p = oftype(n, 2)
    while p * p <= n
        e = 0
        while n % p == 0; n = div(n, p); e += 1; end
        isodd(e) && (s *= p)
        p += 1
    end
    return s * n
end
sqfree(x::Rational) = sqfree(numerator(x)) * sqfree(denominator(x)) |> sqfree

function legendre(a::Integer, p::Integer)
    a = mod(a, p)
    a == 0 && return 0
    return powermod(a, div(p - 1, 2), p) == 1 ? 1 : -1
end

function vp_unit(a::Integer, p::Integer)
    e = 0
    while a % p == 0; a = div(a, p); e += 1; end
    return e, a
end

"(a,b)_p for nonzero integers or rationals; p a prime, or 0 for the real place."
function hilbert(a, b, p::Integer)
    a = sqfree(a); b = sqfree(b)
    p == 0 && return (a < 0 && b < 0) ? -1 : 1
    al, u = vp_unit(a, p); be, v = vp_unit(b, p)
    if p == 2
        e(x) = mod(div(x - 1, 2), 2)             # x odd
        w(x) = mod(div(x * x - 1, 8), 2)
        u8 = mod(u, 8); v8 = mod(v, 8)
        return isodd(e(u8) * e(v8) + al * w(v8) + be * w(u8)) ? -1 : 1
    end
    r = 1
    (isodd(al) && isodd(be) && p % 4 == 3) && (r = -r)
    isodd(be) && (r *= legendre(u, p))
    isodd(al) && (r *= legendre(v, p))
    return r
end

"Discriminant modulo squares (a squarefree integer)."
function disc(q)
    d = 1
    for a in q; d = sqfree(d * sqfree(a)); end
    return d
end

function hasse(q, p::Integer)
    s = [sqfree(a) for a in q]; r = 1
    for i in 1:length(s), j in i+1:length(s)
        r *= hilbert(s[i], s[j], p)
    end
    return r
end

sig(q) = (count(>(0), q), count(<(0), q))

"2 and the primes dividing the squarefree part of an entry of one of the forms."
function relevant_primes(forms...)
    ps = Set{Int}([2])
    for q in forms, a in q
        union!(ps, Int.(primes_of(sqfree(a))))
    end
    return sort!(collect(ps))
end

"Is x a square in Q_p (p = 0: in R)?"
function is_square_Qp(x, p::Integer)
    s = sqfree(x)
    p == 0 && return s > 0
    e, u = vp_unit(s, p)
    e != 0 && return false
    return p == 2 ? mod(u, 8) == 1 : legendre(u, p) == 1
end

"Isometry over Q (Hasse-Minkowski)."
function isometric(q1, q2)
    (length(q1) == length(q2) && sig(q1) == sig(q2) && disc(q1) == disc(q2)) || return false
    return all(hasse(q1, p) == hasse(q2, p) for p in relevant_primes(q1, q2))
end

"""
The local data (d', Dict(p => eps'_p)) of a complement W' with V = T + W':
d' = d(V) d(T), eps'_p = eps_p(V) eps_p(T) (d(T), d')_p, at the relevant primes.
"""
function complement_data(T, V)
    dW = sqfree(disc(V) * disc(T))
    ps = sort!(unique!(vcat(relevant_primes(T, V), Int.(primes_of(dW)))))
    dT = disc(T)
    return dW, Dict(p => hasse(V, p) * hasse(T, p) * hilbert(dT, dW, p) for p in ps), ps
end

"""
Does the rational quadratic space T embed isometrically in V?  (Witt
cancellation and Hasse-Minkowski; Serre, Ch. IV, Prop. 6 and 7: a form of
rank k with prescribed signature, discriminant d' and local invariants
exists iff the signs agree, the product formula holds, and locally
k >= 3, or k = 2 and (d', eps') != (-1, -1), or k = 1 and eps' = 1.)
"""
function embeds(T, V)
    k = length(V) - length(T)
    sT, sV = sig(T), sig(V)
    (k < 0 || sT[1] > sV[1] || sT[2] > sV[2]) && return false
    k == 0 && return isometric(T, V)
    k >= 3 && return true
    dW, eps, ps = complement_data(T, V)
    k == 1 && return all(eps[p] == 1 for p in ps)
    return all(eps[p] == 1 for p in ps if is_square_Qp(-dW, p))
end

scale(q, lam) = [a * lam for a in q]

"""
Diagonal entries of a diagonalisation of the nondegenerate symmetric
rational matrix G (exact congruence operations).
"""
function diagonalize(G0::AbstractMatrix)
    n = size(G0, 1)
    M = Rational{BigInt}.(G0)
    @assert M == transpose(M)
    out = Rational{BigInt}[]
    for i in 1:n
        if M[i, i] == 0
            j = findfirst(k -> M[k, k] != 0, i+1:n)
            if j !== nothing                      # swap basis vectors i and j
                j += i
                M[[i, j], :] = M[[j, i], :]; M[:, [i, j]] = M[:, [j, i]]
            else                                  # e_i -> e_i + e_j with G[i,j] != 0
                j = findfirst(k -> M[i, k] != 0, i+1:n)
                @assert j !== nothing "degenerate form"
                j += i
                M[i, :] += M[j, :]; M[:, i] += M[:, j]
            end
        end
        d = M[i, i]; @assert d != 0
        push!(out, d)
        for r in i+1:n
            f = M[r, i] / d
            f == 0 && continue
            M[r, :] -= f * M[i, :]
        end
        for c in i+1:n
            f = M[i, c] / d
            f == 0 && continue
            M[:, c] -= f * M[:, i]
        end
    end
    return out
end

# ---- the PASS/FAIL convention shared by the programs of this directory -------
mutable struct Checks
    file::String
    passed::Int
    failed::Int
end
Checks(file) = Checks(file, 0, 0)
function check(c::Checks, name, ok::Bool)
    ok ? (c.passed += 1) : (c.failed += 1)
    println(ok ? "PASS " : "FAIL ", name)
    flush(stdout)
    return ok
end
function finish(c::Checks)
    println(c.file, ": ", c.passed, " checks passed, ", c.failed, " failed")
    exit(c.failed > 0 ? 1 : 0)
end

end # module

# ---- run alone: the checks of hilbert.c (Table II of the paper) ---------------
using .QuadraticForms
function quadratic_forms_selftest()
    C = Checks("quadratic_forms.jl")
    # T = Tr_{E/Q} q_E diagonalised modulo squares; <1,-10>; T + <1,-10>;
    # V3 = U^3 + A_2(-1)^2 with A_2(-1) = <-2,-6>; V2 = U^3 + E8(-2) = U^3 + <-2>^8.
    Tf = [-1, -6, -1, -6, -1, 3, -2, 15]
    forms = [("T", Tf), ("<1,-10>", [1, -10]), ("T+<1,-10>", vcat(Tf, [1, -10])),
             ("V3", [1, -1, 1, -1, 1, -1, -2, -6, -2, -6]),
             ("V2", vcat([1, -1, 1, -1, 1, -1], fill(-2, 8)))]
    # Table II: rank, number of positive entries, d, eps_2, eps_3, eps_5
    table = [(8, 2, 10, 1, -1, 1), (2, 1, -10, 1, 1, 1), (10, 3, -1, 1, -1, 1),
             (10, 3, -1, 1, -1, 1), (14, 3, -1, -1, 1, 1)]
    for ((name, q), row) in zip(forms, table)
        got = (length(q), sig(q)[1], disc(q), hasse(q, 2), hasse(q, 3), hasse(q, 5))
        check(C, "$name: rank $(got[1]) signature $(sig(q)) d=$(got[3]) eps_2=$(got[4]) eps_3=$(got[5]) eps_5=$(got[6]) matches Table II", got == row)
    end
    check(C, "eps_p = 1 for the five forms at every prime 7 <= p < 100",
          all(hasse(q, p) == 1 for (_, q) in forms for p in 7:99 if length(primes_of(p)) == 1 && primes_of(p)[1] == p))
    check(C, "T + <1,-10> isometric to V3 over Q", isometric(forms[3][2], forms[4][2]))
    P = [2, 3, 5, 7]
    ok = true
    for a in -30:30, b in -30:30
        (a == 0 || b == 0) && continue
        x = abs(sqfree(a) * sqfree(b))
        for p in P; while x % p == 0; x = div(x, p); end; end
        x == 1 || continue
        ok &= hilbert(a, b, 0) * prod(hilbert(a, b, p) for p in P) == 1
    end
    check(C, "product formula on pairs with primes in {2,3,5,7}, |a|,|b| <= 30", ok)
    ok = true; npairs = 0
    for a in -400:400, b in -400:400
        (a == 0 || b == 0) && continue
        npairs += 1
        ps = vcat(0, sort!(unique!(vcat(2, primes_of(a), primes_of(b)))))
        ok &= prod(hilbert(a, b, p) for p in ps) == 1
        ok &= all(hilbert(a, -a, p) == 1 && hilbert(a, b, p) == hilbert(b, a, p) for p in ps)
        if a != 1
            ok &= all(hilbert(a, 1 - a, p) == 1 for p in vcat(0, 2, primes_of(a), primes_of(1 - a)))
        end
    end
    check(C, "product formula, (a,-a)_p = 1, symmetry, (a,1-a)_p = 1 on $npairs pairs with |a|,|b| <= 400", ok)
    check(C, "(-1,-1)_2 = -1, (-1,-1)_3 = 1, (2,6)_3 = -1, (2,2)_2 = 1, (2,3)_2 = -1, (3,3)_3 = -1",
          hilbert(-1, -1, 2) == -1 && hilbert(-1, -1, 3) == 1 && hilbert(2, 6, 3) == -1 &&
          hilbert(2, 2, 2) == 1 && hilbert(2, 3, 2) == -1 && hilbert(3, 3, 3) == -1)
    finish(C)
end
if abspath(PROGRAM_FILE) == (@__FILE__)
    quadratic_forms_selftest()
end
