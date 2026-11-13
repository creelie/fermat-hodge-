# Theorem thm:secantintegral: integral classes on the secant planes B_Q(h,q) of a complex 4-torus.
# (1) For 40 pseudo-random integral alternating forms h on Z^8, the gcd D_k of the coefficients of h^[k] = h^k/k!
#     satisfies D_k^2 = gcd of all 2k x 2k minors of the matrix of h, i.e. D_k = d_1...d_k (Frobenius normal form);
# (2) for 9 types (d_1,...,d_4) and every q = n/d with 1 <= n, d <= 24 coprime, the generators r_0 alpha, s_0 beta of
#     B_Q(h,q) cap H(X,Z) have chi in 8Z, and the least |chi| is 8;
# (3) E^4, h = e_1+e_2+e_3-e_4, q = 1/4: the lattice is 16Z alpha + 4Z beta, chi = -128, -32; beta is not integral;
# (4) on the twisted planes exp(-th)B_Q(h,q), Pf(h) < 0, no integral class with chi = -2 has coordinates
#     x_k = c_k D_k in the box |x_k| <= 6 for 10 divisor types (a search; no statement rests on it).
# Exact integer and Rational{BigInt} arithmetic; the pseudo-random generator is a fixed linear congruential sequence.
include(joinpath(@__DIR__, "quadratic_forms.jl")); using .QuadraticForms
const QQ = Rational{BigInt}

# Pfaffian of a principal submatrix = coefficient of g_I in h^[k]
function pfaff(M::Matrix{BigInt}, I::Vector{Int})
    isempty(I) && return big(1)
    s = big(0); i1 = I[1]
    for t in 2:length(I)
        J = [I[u] for u in 2:length(I) if u != t]
        s += (iseven(t) ? 1 : -1) * M[i1, I[t]] * pfaff(M, J)
    end
    s
end
function detb(A::Matrix{BigInt})            # Bareiss
    A = copy(A); n = size(A, 1); sgn = 1; prev = big(1)
    for k in 1:n-1
        if A[k, k] == 0
            p = findfirst(i -> A[i, k] != 0, k+1:n)
            p === nothing && return big(0)
            p += k; A[[k, p], :] = A[[p, k], :]; sgn = -sgn
        end
        for i in k+1:n, j in k+1:n
            A[i, j] = div(A[i, j] * A[k, k] - A[i, k] * A[k, j], prev)
        end
        prev = A[k, k]
    end
    sgn * A[n, n]
end
combs(N, k) = k == 0 ? [Int[]] : [vcat(s, [x]) for s in combs(N, k - 1) for x in (isempty(s) ? 1 : s[end] + 1):N]

C = Checks("lattice.jl")
let seed = UInt64(20261113), ok = true
    vals = [0, 0, 1, -1, 2, -2, 3, 4, 6]
    nextval() = (seed = seed * 6364136223846793005 + 1442695040888963407; vals[Int((seed >> 33) % 9) + 1])
    for trial in 1:40
        M = zeros(BigInt, 8, 8)
        for i in 1:8, j in i+1:8
            v = nextval(); M[i, j] = v; M[j, i] = -v
        end
        for k in 1:4
            Dk = reduce(gcd, [pfaff(M, I) for I in combs(8, 2k)]; init=big(0))
            Mk = reduce(gcd, [detb(M[I, J]) for I in combs(8, 2k) for J in combs(8, 2k)]; init=big(0))
            ok &= Dk^2 == Mk
        end
    end
    check(C, "40 integral 2-forms on Z^8: (gcd of coefficients of h^[k])^2 = gcd of 2k x 2k minors, k = 1..4", ok)
end

function rgcd(us)
    us = [QQ(u) for u in us if !iszero(u)]
    QQ(reduce(gcd, numerator.(us)), reduce(lcm, denominator.(us)))
end
function lattice_gens(ds, q)
    D = [1, ds[1], ds[1] * ds[2], ds[1] * ds[2] * ds[3], prod(ds)]
    r0 = 1 / rgcd([1, q * D[3], q^2 * D[5]])      # alpha = 1 - q h^[2] + q^2 h^[4]
    s0 = 1 / rgcd([D[2], q * D[4]])               # beta = h - q h^[3]
    r0, s0, 8 * q^2 * r0^2 * D[5], 8 * q * s0^2 * D[5]
end
let ok = true, minabs = nothing
    for ds in [(1,1,1,1), (1,1,1,2), (1,1,2,2), (1,2,2,2), (1,1,1,4), (1,2,4,8), (2,2,2,2), (1,1,3,3), (1,3,3,3)]
        for qn in 1:24, qd in 1:24
            gcd(qn, qd) == 1 || continue
            _, _, cr, cs = lattice_gens(ds, QQ(qn, qd))
            for v in (cr, cs)
                ok &= denominator(v) == 1 && mod(numerator(v), 8) == 0
                minabs = minabs === nothing ? abs(v) : min(minabs, abs(v))
            end
        end
    end
    check(C, "lattice generators have chi in 8Z (9 divisor types, q = n/d, n,d <= 24); least |chi| = $minabs", ok && minabs == 8)
end
let (r0, s0, cr, cs) = lattice_gens((1, 1, 1, 1), QQ(1, 4))
    check(C, "E^4, h = e1+e2+e3-e4, q = 1/4: lattice $(r0) alpha + $(s0) beta, chi = $(-cr), $(-cs)",
          r0 == 16 && s0 == 4 && -cr == -128 && -cs == -32)
end
let found = 0, B = 6
    for ds in [(1,1,1,1), (1,1,1,2), (1,1,2,2), (1,2,2,2), (1,1,1,3), (1,1,3,3), (1,1,1,4), (1,1,2,4), (1,2,2,4), (2,2,2,2)]
        D = [1, ds[1], ds[1] * ds[2], ds[1] * ds[2] * ds[3], prod(ds)]; Pf = -D[5]
        for x0 in -B:B, x1 in -B:B, x2 in -B:B, x3 in -B:B
            c0, c1, c2, c3 = QQ(x0), QQ(x1, D[2]), QQ(x2, D[3]), QQ(x3, D[4])
            det = c1^2 - c0 * c2
            iszero(det) && continue
            T = (c2 * c1 - c3 * c0) / det; N = (c2^2 - c1 * c3) / det
            T^2 >= 4N && continue
            c4 = T * c3 - N * c2
            denominator(c4 * D[5]) == 1 || continue
            Pf * (2c0 * c4 - 8c1 * c3 + 6c2^2) == -2 && (found += 1)
        end
    end
    check(C, "twisted planes, Pf < 0, box |x_k| <= 6, 10 divisor types: $found integral classes with chi = -2", found == 0)
end
finish(C)
