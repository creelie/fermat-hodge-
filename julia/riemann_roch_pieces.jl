# riemann_roch_pieces.jl -- port of code/riemann_roch_pieces.py: Riemann-Roch
# constraints on the Ext groups of the pieces of thm:product, A a Weil
# fourfold (principal polarisation theta, int theta^4 = 4!).
#
# (A) For p = sum_k c_k theta^k, chi(F, L^l) = int p(-theta) e^{l theta} =
#     P_c(l) = sum_k (-1)^k c_k 4!/(4-k)! l^(4-k), and p = sum_l b_l e^{l theta}
#     mod theta^5 with b = V^{-1} c, V_{jl} = l^j/j!.  For every nonempty
#     subset S of {0..4} the linear system { b_l(c) = 0 (l not in S),
#     P_c(s) = 0 (s in S) } is solved exactly, and S is admissible if some
#     solution c has b_l(c) != 0 for all l in S.  (The Python concludes
#     that the admissible supports are the five singletons.)
#     Admissibility is decided exactly: the solutions form a linear space N,
#     and a c in N with all b_l(c) != 0 (l in S) exists iff no linear form
#     b_l (l in S) vanishes identically on N (a vector space over Q is not a
#     finite union of proper subspaces).  The Python tests the basis vectors
#     of N and then a generic combination, which decides the same question.
# (B) chi(E,E) for ch(E) = M w + sum_k mu_k e^{k theta} on the sixfold: the
#     polynomial sum_{k,j} mu_k mu_j (j-k)^6, its value at mu = (1,1,1).
# (C) the squares of the differences of the classes c_1 of the pieces on A'.
# Exact arithmetic over Q.
# Run: julia --startup-file=no riemann_roch_pieces.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms: Checks, check, finish

const Q = Rational{BigInt}

"reduced row echelon form; returns (R, pivot columns)"
function rref(A::Matrix{Q})
    R = copy(A); m, n = size(R); piv = Int[]; r = 1
    for c in 1:n
        r > m && break
        p = findfirst(i -> R[i, c] != 0, r:m)
        p === nothing && continue
        p += r - 1
        R[[r, p], :] = R[[p, r], :]
        R[r, :] /= R[r, c]
        for i in 1:m
            (i != r && R[i, c] != 0) && (R[i, :] -= R[i, c] * R[r, :])
        end
        push!(piv, c); r += 1
    end
    return R, piv
end
"basis of the null space of A (columns of the returned matrix)"
function nullspace(A::Matrix{Q})
    R, piv = rref(A); n = size(A, 2)
    free = [c for c in 1:n if !(c in piv)]
    N = zeros(Q, n, length(free))
    for (k, f) in enumerate(free)
        N[f, k] = 1
        for (i, c) in enumerate(piv); N[c, k] = -R[i, f]; end
    end
    return N
end
function inverse(A::Matrix{Q})
    n = size(A, 1); R, piv = rref(hcat(A, Matrix{Q}(Q(1) * (1:n .== (1:n)'))))
    @assert piv == collect(1:n)
    return R[:, n+1:2n]
end

function subsets_of_size(n, k)                       # subsets of 0..n-1, lexicographic
    out = Vector{Vector{Int}}()
    function rec(start, cur)
        length(cur) == k && (push!(out, copy(cur)); return)
        for i in start:n-1
            push!(cur, i); rec(i + 1, cur); pop!(cur)
        end
    end
    rec(0, Int[])
    return out
end

function main()
    C = Checks("riemann_roch_pieces.jl")
    # ---- (A) -----------------------------------------------------------------------
    # P(l) = sum_k Pc[k] l^(4-k) c_k with Pc[k] = (-1)^k 4!/(4-k)!
    Pc = [Q((-1)^k * factorial(4) // factorial(4 - k)) for k in 0:4]
    check(C, "chi(F, L^l) = P(l) = 24 c4 - 24 c3 l + 12 c2 l^2 - 4 c1 l^3 + c0 l^4", Pc == Q[1, -4, 12, -24, 24])
    Prow(s) = Q[Pc[k+1] * Q(s)^(4 - k) for k in 0:4]  # the linear form c -> P_c(s)
    V = Q[Q(L)^j // factorial(j) for j in 0:4, L in 0:4]   # V b = c
    B = inverse(V)                                   # b = B c
    check(C, "V B = 1 for V_{jl} = l^j/j! (the exponential expansion p = sum_l b_l e^{l theta} mod theta^5)",
          V * B == Matrix{Q}(Q(1) * (1:5 .== (1:5)')))
    println("    exponential coefficients b_l (rows; columns c0..c4): ")
    for L in 0:4; println("      b_$L = ", [string(numerator(x), denominator(x) == 1 ? "" : "/$(denominator(x))") for x in B[L+1, :]]); end
    # e^{l theta} itself: c_k = l^k/k!, b = unit vector, and P(l') = (l' - l)^4
    check(C, "for p = e^{l theta}: b = e_l and chi(F, L^l') = (l' - l)^4, l, l' = 0..4",
          all(B * Q[Q(L)^k // factorial(k) for k in 0:4] == Q[i == L ? 1 : 0 for i in 0:4] &&
              all(sum(Prow(s) .* Q[Q(L)^k // factorial(k) for k in 0:4]) == Q(s - L)^4 for s in 0:4) for L in 0:4))
    admissible = Vector{Vector{Int}}(); nsub = 0; dims = Dict{Vector{Int},Int}()
    for size in 1:5, S in subsets_of_size(5, size)
        nsub += 1
        rows = vcat([B[L+1:L+1, :] for L in 0:4 if !(L in S)]..., [reshape(Prow(s), 1, 5) for s in S]...)
        N = nullspace(Matrix{Q}(rows))
        dims[S] = Base.size(N, 2)
        # admissible iff no b_l (l in S) vanishes identically on the solution space
        ok = Base.size(N, 2) > 0 && all(any(x -> x != 0, B[L+1:L+1, :] * N) for L in S)
        ok && push!(admissible, S)
        println("    S=", S, ": nullspace dim ", Base.size(N, 2), "; admissible c (b!=0 on S, P=0 on S): ", ok)
    end
    println("    admissible supports: ", admissible)
    check(C, "31 nonempty subsets S of {0..4}; the admissible supports are exactly the five singletons (p = b e^{l theta})",
          nsub == 31 && sort(admissible) == [[l] for l in 0:4])
    check(C, "for the singletons the solution space is the line Q e^{l theta}; for |S| >= 2 the system has only the solution c = 0",
          all(dims[[l]] == 1 for l in 0:4) && all(dims[S] == 0 for S in keys(dims) if length(S) >= 2))

    # ---- (B) -----------------------------------------------------------------------
    # chi(E,E) = 2 M^2 |x|^2 + sum_{k,j} mu_k mu_j (j-k)^6
    coef = Dict{Tuple{Int,Int},Int}()
    for k in 0:2, j in 0:2
        key = (min(k, j), max(k, j)); coef[key] = get(coef, key, 0) + (j - k)^6
    end
    println("(B) chi(E,E) = 2 M^2 |x|^2 + ", join(["$(c) mu$(k) mu$(j)" for ((k, j), c) in sort(collect(coef)) if c != 0], " + "))
    check(C, "chi(E,E) - 2M^2|x|^2 = 2 mu0 mu1 + 128 mu0 mu2 + 2 mu1 mu2, equal to 132 at mu = (1,1,1)",
          coef[(0, 1)] == 2 && coef[(0, 2)] == 128 && coef[(1, 2)] == 2 && coef[(0, 0)] == coef[(1, 1)] == coef[(2, 2)] == 0 &&
          sum(values(coef)) == 132)

    # ---- (C) -----------------------------------------------------------------------
    # classes (a1, a2, r) = a1 om'_1 + a2 om'_2 + r th' with coefficients polynomials in N1, N2, r1, r2;
    # D^2 = -2 u2 a1^2 - 2 D u2 a2^2 + 2 r^2  (u2 = |u'|^2).  The symbols N1, N2, r1, r2, u2, D are
    # kept formal: a class is a triple of integer vectors over (1, N1, N2, r1, r2).
    names = ["1", "N1", "N2", "r1", "r2"]
    e(i) = Int[j == i ? 1 : 0 for j in 1:5]; z5 = zeros(Int, 5)
    cls = ["N1" => (e(2), z5, e(4)), "N2" => (z5, e(3), e(5)), "O" => (z5, z5, z5), "L'" => (z5, z5, e(1)), "L'^2" => (z5, z5, 2e(1))]
    sqr(x) = Dict((min(i, j), max(i, j)) => (i == j ? 1 : 2) * x[i] * x[j] for i in 1:5 for j in i:5 if x[i] * x[j] != 0)
    function term(d, pre)
        isempty(d) && return ""
        join(["$(pre * c) " * (names[i] == "1" ? (names[j] == "1" ? "" : names[j]) : names[i] * (i == j ? "^2" : "*" * names[j])) for ((i, j), c) in sort(collect(d))], " + ")
    end
    ok = true
    println("(C) c_1(Y') - c_1(Y) squared (|u'|^2 = u2):")
    for (Y, cy) in cls, (Yp, cyp) in cls
        d = (cyp[1] - cy[1], cyp[2] - cy[2], cyp[3] - cy[3])
        s1, s2, s3 = sqr(d[1]), sqr(d[2]), sqr(d[3])
        parts = filter(!isempty, ["u2*(" * term(s1, -2) * ")", "D*u2*(" * term(s2, -2) * ")", term(s3, 2)])
        parts = [p for p in parts if !endswith(p, "()")]
        println("      Ext^*(", rpad(Y, 5), ",", rpad(Yp, 5), "): D^2 = ", isempty(parts) ? "0" : join(parts, " + "))
        # symmetry D -> -D and the value on the diagonal
        ok &= sqr(-d[1]) == s1 && sqr(-d[2]) == s2 && sqr(-d[3]) == s3
        Y == Yp && (ok &= isempty(s1) && isempty(s2) && isempty(s3))
    end
    check(C, "the 25 squares D^2 = -2 u2 a1^2 - 2 D u2 a2^2 + 2 r^2 of the differences of the five classes: zero on the diagonal, symmetric", ok)
    d = (z5, z5, 2e(1) - e(1)); check(C, "(L'^2 - L')^2 = 2 and (L'^2 - O)^2 = 8 (theta'^2 = 2)", sqr(d[3]) == Dict((1, 1) => 1) && sqr(2e(1)) == Dict((1, 1) => 4))
    finish(C)
end
main()
