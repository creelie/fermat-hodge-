# zeta_invariants.jl -- port of code/zeta7_invariants.py and code/zeta9_invariants.py.
#
# F = Q(theta) a cyclic cubic field, theta = zeta_n + zeta_n^{-1}, n = 7 or 9.
# For a quaternion algebra (a,b)_F and c in F the form Tr_{F/Q}(c nrd) of rank 12
# is computed in the basis theta^m {1,i,j,k} (nrd = <1,-a,-b,ab>), diagonalised,
# and compared by rank, signature, discriminant and Hasse invariants at all
# primes below 60 with
#   n = 7:  U^2 + E_8(-1)  (the transcendental space of the family of Theorem
#           thm:zeta9 at n = 7), predicted to be Tr(theta nrd_{(-1,theta)});
#   n = 9:  (U + A_2(-1)^4)^perp in the K3 lattice, predicted to be
#           Tr(-theta nrd_{(-1,-theta)}).
# Also the Dickson identities of Step 1 and the order of 2 in (Z/n)^x/{+-1}.
# Exact arithmetic (Rational{BigInt}); total positivity is decided from the
# signs of the coefficients of the characteristic polynomial (all roots are
# real), where the Python evaluates at floating-point roots.
# Run: julia --startup-file=no zeta_invariants.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms

const Q = Rational{BigInt}

# ---- the cubic field Q[th]/(th^3 + c2 th^2 + c1 th + c0), elements as coefficient vectors
struct Cubic
    c2::Int; c1::Int; c0::Int
end
function mul(F::Cubic, x::Vector{Q}, y::Vector{Q})
    r = zeros(Q, 5)
    for i in 1:3, j in 1:3; r[i+j-1] += x[i] * y[j]; end
    for k in (5, 4)                                  # th^(k-1) = -c2 th^(k-2) - c1 th^(k-3) - c0 th^(k-4)
        c = r[k]; r[k] = 0
        r[k-1] -= F.c2 * c; r[k-2] -= F.c1 * c; r[k-3] -= F.c0 * c
    end
    return r[1:3]
end
el(x...) = Q[x...]
const ONE = el(1, 0, 0); const TH = el(0, 1, 0)
mulmat(F, x) = hcat(mul(F, x, el(1, 0, 0)), mul(F, x, el(0, 1, 0)), mul(F, x, el(0, 0, 1)))
tr(F, x) = (M = mulmat(F, x); M[1, 1] + M[2, 2] + M[3, 3])
function charpoly_coeffs(F, x)                       # x^3 - t x^2 + s x - n
    M = mulmat(F, x); M2 = M * M
    t = M[1, 1] + M[2, 2] + M[3, 3]
    s = (t * t - (M2[1, 1] + M2[2, 2] + M2[3, 3])) / 2
    n = M[1, 1] * (M[2, 2] * M[3, 3] - M[2, 3] * M[3, 2]) - M[1, 2] * (M[2, 1] * M[3, 3] - M[2, 3] * M[3, 1]) +
        M[1, 3] * (M[2, 1] * M[3, 2] - M[2, 2] * M[3, 1])
    return t, s, n
end
"number of positive conjugates of x != 0 (the three conjugates are real): Descartes' rule, exact here"
function npositive(F, x)
    t, s, n = charpoly_coeffs(F, x)
    @assert n != 0
    c = [1, -t, s, -n]; c = [v for v in c if v != 0]
    return count(i -> sign(c[i]) != sign(c[i+1]), 1:length(c)-1)   # all roots real: sign changes = positive roots
end
totally_positive(F, x) = npositive(F, x) == 3

"Gram matrix of Tr_{F/Q}(c nrd) on (a,b)_F, basis theta^m {1,i,j,k}, nrd = <1,-a,-b,ab>."
function trace_form(F, c, a, b)
    dg = [ONE, -a, -b, mul(F, a, b)]
    pw = [ONE, TH, mul(F, TH, TH)]; push!(pw, mul(F, pw[3], TH)); push!(pw, mul(F, pw[4], TH))
    G = zeros(Q, 12, 12)
    for s in 0:3, m in 0:2, n in 0:2
        G[3s+m+1, 3s+n+1] = tr(F, mul(F, mul(F, c, dg[s+1]), pw[m+n+1]))
    end
    return G
end

const PRIMES = [p for p in 2:59 if all(p % q != 0 for q in 2:isqrt(p))]
"(signature, discriminant, Hasse invariants at the primes below 60) of a diagonal form"
invariants(D) = (sig(D), disc(D), [hasse(D, p) for p in PRIMES])
"invariants of W' with V = W + W' (Witt cancellation)"
function complement_invariants(V, W)
    sV, dV, eV = invariants(V); sW, dW, eW = invariants(W)
    d = sqfree(dV * dW)
    return ((sV[1] - sW[1], sV[2] - sW[2]), d, [eV[i] * eW[i] * hilbert(dW, d, p) for (i, p) in enumerate(PRIMES)])
end
bad(inv) = [p for (i, p) in enumerate(PRIMES) if inv[3][i] == -1]
show_inv(inv) = "signature $(inv[1]), d = $(inv[2]), Hasse invariant -1 at $(bad(inv))"

# ---- Laurent polynomials in several variables, Dict(exponents => coefficient)
const LP = Dict{Vector{Int},Q}
const NV = 5                                         # variables v, a, t, mu, z
var(i) = LP(Int[j == i ? 1 : 0 for j in 1:NV] => Q(1))
cst(c) = c == 0 ? LP() : LP(zeros(Int, NV) => Q(c))
function padd(x::LP, y::LP, s = 1)
    r = copy(x)
    for (k, c) in y
        v = get(r, k, Q(0)) + s * c
        v == 0 ? delete!(r, k) : (r[k] = v)
    end
    return r
end
function pmul(x::LP, y::LP)
    r = LP()
    for (k1, c1) in x, (k2, c2) in y
        k = k1 + k2; v = get(r, k, Q(0)) + c1 * c2
        v == 0 ? delete!(r, k) : (r[k] = v)
    end
    return r
end
ppow(x::LP, n::Int) = n == 0 ? cst(1) : pmul(x, ppow(x, n - 1))
pinv_monomial(x::LP) = (@assert length(x) == 1; (k, c) = first(x); LP(-k => 1 / c))
"substitute variable i by the Laurent polynomial y (i occurs with exponents >= 0 unless y is a monomial)"
function psubs(x::LP, i::Int, y::LP)
    r = LP()
    for (k, c) in x
        k0 = copy(k); e = k0[i]; k0[i] = 0
        r = padd(r, pmul(LP(k0 => c), e >= 0 ? ppow(y, e) : ppow(pinv_monomial(y), -e)))
    end
    return r
end
"coefficient of t^e (variable i), as a Laurent polynomial in the other variables"
function pcoeff(x::LP, i::Int, e::Int)
    r = LP()
    for (k, c) in x
        k[i] == e || continue
        k0 = copy(k); k0[i] = 0; r[k0] = c
    end
    return r
end

function main()
    C = Checks("zeta_invariants.jl")
    E8 = [2 -1 0 0 0 0 0 0; -1 2 -1 0 0 0 0 0; 0 -1 2 -1 0 0 0 0; 0 0 -1 2 -1 0 0 0;
          0 0 0 -1 2 -1 0 -1; 0 0 0 0 -1 2 -1 0; 0 0 0 0 0 -1 2 0; 0 0 0 0 -1 0 0 2]
    U = Q[1, -1]
    Lam = vcat(fill(Q(1), 3), fill(Q(-1), 19))       # the K3 lattice over Q

    # ================= n = 7 (zeta7_invariants.py) ==================================
    check(C, "det E_8 = 1", prod(diagonalize(E8)) == 1)
    dE8m = diagonalize(-E8)
    direct = invariants(vcat(U, U, dE8m))
    witt = complement_invariants(Lam, vcat(U, dE8m))
    println("U^2 + E_8(-1): direct: ", show_inv(direct), "; by Witt cancellation: ", show_inv(witt))
    check(C, "U^2 + E_8(-1): signature (2,10), d = 1, Hasse invariant -1 exactly at 2 among p < 60, directly and by Witt cancellation in the K3 lattice",
          direct == witt == ((2, 10), 1, [p == 2 ? -1 : 1 for p in PRIMES]))
    F7 = Cubic(1, -2, -1)                            # th^3 + th^2 - 2 th - 1
    check(C, "n = 7: theta^3 + theta^2 - 2 theta - 1 = 0 and theta has exactly one positive conjugate",
          mul(F7, TH, mul(F7, TH, TH)) + mul(F7, TH, TH) - 2TH - ONE == el(0, 0, 0) && npositive(F7, TH) == 1)
    pred = invariants(diagonalize(trace_form(F7, TH, -ONE, TH)))
    println("Tr(theta nrd_{(-1,theta)}): ", show_inv(pred))
    check(C, "n = 7: Tr(theta nrd_{(-1,theta)}) has the invariants of U^2 + E_8(-1)", pred == direct)
    for (label, (c, a, b)) in ["(-1,-theta), c=-theta" => (-TH, -ONE, -TH), "(-1,theta), c=-theta" => (-TH, -ONE, TH)]
        inv = invariants(diagonalize(trace_form(F7, c, a, b)))
        println("contrast ", label, ": ", show_inv(inv))
        check(C, "n = 7: the contrast $label differs from U^2 + E_8(-1)", inv != direct)
    end
    # algebras (-1, theta u), u totally positive: same real ramification; the finitely ramified ones differ
    bad_primes = Set{Int}(); matched = 0; others = 0; shape = true
    for x in -2:2, y in -2:2, z in -2:2
        u = el(x, y, z)
        (u == el(0, 0, 0) || !totally_positive(F7, u)) && continue
        tu = mul(F7, TH, u)
        inv = invariants(diagonalize(trace_form(F7, tu, -ONE, tu)))
        if inv == direct
            matched += 1
        else
            others += 1
            shape &= inv[1] == (2, 10) && inv[2] == 1
            union!(bad_primes, bad(inv))
        end
    end
    println("competitors with the same real ramification: matched ", matched, ", others ", others, "; the others differ at ", sort(collect(bad_primes)))
    check(C, "n = 7: among (-1, theta u), u totally positive with coefficients in [-2,2], some match ($matched); the others ($others) have signature (2,10), d = 1 and differ at primes in {7, 43}, 7 among them",
          matched > 0 && shape && issubset(bad_primes, [7, 43]) && 7 in bad_primes)

    # Dickson identities (Step 1) and the inertness of 2
    v, a, t, mu, z = var(1), var(2), var(3), var(4), var(5)
    lin(terms...) = reduce(padd, [pmul(cst(c), m) for (c, m) in terms])
    p7 = lin((1, ppow(t, 7)), (-7, pmul(a, ppow(t, 5))), (14, pmul(ppow(a, 2), ppow(t, 3))), (-7, pmul(ppow(a, 3), t)))
    av = pmul(a, pinv_monomial(v))                    # a/v
    check(C, "p_{7,a}(v + a/v) = v^7 + (a/v)^7",
          isempty(padd(padd(psubs(p7, 3, padd(v, av)), ppow(v, 7), -1), ppow(av, 7), -1)))
    check(C, "p_{7,a}(mu t) = mu^7 p_{7,a/mu^2}(t)",
          isempty(padd(psubs(p7, 3, pmul(mu, t)), pmul(ppow(mu, 7), psubs(p7, 2, pmul(a, ppow(pinv_monomial(mu), 2)))), -1)))
    dif = padd(psubs(p7, 3, pmul(z, t)), p7, -1)
    check(C, "p_{7,a}(zeta t) - p_{7,a}(t) has t^7 coefficient zeta^7 - 1 and t^5 coefficient -7a(zeta^5 - 1)",
          pcoeff(dif, 3, 7) == padd(ppow(z, 7), cst(1), -1) && pcoeff(dif, 3, 5) == pmul(pmul(cst(-7), a), padd(ppow(z, 5), cst(1), -1)))
    p9 = lin((1, ppow(t, 9)), (-9, pmul(a, ppow(t, 7))), (27, pmul(ppow(a, 2), ppow(t, 5))), (-30, pmul(ppow(a, 3), ppow(t, 3))), (9, pmul(ppow(a, 4), t)))
    check(C, "p_{9,a}(v + a/v) = v^9 + (a/v)^9",
          isempty(padd(padd(psubs(p9, 3, padd(v, av)), ppow(v, 9), -1), ppow(av, 9), -1)))
    function order2(n)
        k = 1; x = 2 % n
        while !(x in (1, n - 1)); x = (2x) % n; k += 1; end
        return k
    end
    check(C, "2 has order three in (Z/7)^x/{+-1} and in (Z/9)^x/{+-1}", order2(7) == 3 && order2(9) == 3)

    # ================= n = 9 (zeta9_invariants.py) ==================================
    F9 = Cubic(0, -3, 1)                             # th^3 - 3 th + 1
    check(C, "n = 9: theta^3 - 3 theta + 1 = 0 and theta has exactly two positive conjugates",
          mul(F9, TH, mul(F9, TH, TH)) - 3TH + ONE == el(0, 0, 0) && npositive(F9, TH) == 2)
    Pic = vcat(Q[1, -1], repeat(Q[-2, -3 // 2], 4))  # U + A_2(-1)^4,  A_2(-1) ~ <-2, -3/2>
    @assert Int[sqfree(x) for x in diagonalize([-2 1; 1 -2])] == [-2, -6] == Int[sqfree(x) for x in Q[-2, -3 // 2]]
    target = complement_invariants(Lam, Pic)
    println("T_Q = (U + A_2(-1)^4)^perp: ", show_inv(target))
    check(C, "n = 9: T_Q = (U + A_2(-1)^4)^perp has rank 12, signature (2,10), d = 1, Hasse invariant -1 exactly at 2 among p < 60",
          target == ((2, 10), 1, [p == 2 ? -1 : 1 for p in PRIMES]))
    th2 = el(-2, 1, 0)                               # theta - 2
    cases = ["predicted  D=(-1,-theta), c=-theta" => (-TH, -ONE, -TH),
             "contrast   D=(-1, theta), c= theta" => (TH, -ONE, TH),
             "contrast   D=(-1,-theta), c=-theta*(theta-2) (wrong sign pattern at infinity)" => (-mul(F9, TH, th2), -ONE, -TH),
             "contrast   D=(-theta, -theta+1)" => (mul(F9, ONE - TH, TH), -TH, ONE - TH)]
    for (label, (c, a, b)) in cases
        inv = invariants(diagonalize(trace_form(F9, c, a, b)))
        println(label, ": ", show_inv(inv), "   MATCH=", inv == target)
        check(C, "n = 9: " * (startswith(label, "predicted") ? "Tr(-theta nrd_{(-1,-theta)}) has the invariants of T_Q" :
                              "the " * join(split(label), " ") * " does not match T_Q"),
              startswith(label, "predicted") == (inv == target))
    end
    seen = Dict{Any,Int}(); order = Any[]
    for x in -2:2, y in -2:2, z in -2:2
        u = el(x, y, z)
        (u == el(0, 0, 0) || !totally_positive(F9, u)) && continue
        b = -mul(F9, TH, u)
        inv = invariants(diagonalize(trace_form(F9, b, -ONE, b)))
        haskey(seen, inv) || push!(order, inv)
        seen[inv] = get(seen, inv, 0) + 1
    end
    println("search over b = -theta*u, u totally positive, |x|,|y|,|z| <= 2:")
    for inv in order
        println("  ", show_inv(inv), ": ", seen[inv], " values of u   MATCH=", inv == target)
    end
    check(C, "n = 9: the target invariants occur in the search over (-1, -theta u), u totally positive with coefficients in [-2,2] ($(get(seen, target, 0)) of $(sum(values(seen))))",
          haskey(seen, target))
    finish(C)
end
main()
