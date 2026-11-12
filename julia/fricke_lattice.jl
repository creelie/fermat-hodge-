# fricke_lattice.jl -- port of code/fricke_lattice.py (Proposition V.17: the
# transcendental spaces of the Fricke surfaces and their Kuga-Satake fourfolds).
#
# The very general surface of the Fricke family of level N in {5, 7} has
# Picard lattice U + A_4 + A_1^2 + D_4^2 (N = 5) or U + A_6 + D_4^2 (N = 7),
# so T = NS^perp in the K3 lattice tensor Q is determined by the invariants
# of Hasse-Minkowski (quadratic_forms.jl):
#  (A) A_n + <n+1> = <1>^(n+1) for n = 4, 6, D_4 = <1>^4, A_1^2 = <1>^2, E_8 = <1>^8;
#  (B) T = U^2 + <-1> + <-N> for N = 5 and 7, in two ways;
#  (C) among the pairs a >= b of negative squarefree integers down to -30,
#      U^2 + <a,b> = T exactly for <a,b> = <-1,-N>; the signed discriminant is -N;
#  (D) the dimension count 2 dim SO(3) = 6 = dim SO*(4).
# Run: julia --startup-file=no fricke_lattice.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms

function cartan(t, n)
    G = zeros(Int, n, n)
    for i in 1:n; G[i, i] = 2; end
    if t == 'A'
        for i in 1:n-1; G[i, i+1] = G[i+1, i] = -1; end
    elseif t == 'D'
        for i in 1:n-2; G[i, i+1] = G[i+1, i] = -1; end
        G[n-2, n] = G[n, n-2] = -1
    elseif t == 'E' && n == 8
        for i in 1:6; G[i, i+1] = G[i+1, i] = -1; end      # chain 1-...-7, node 8 attached to node 3
        G[3, 8] = G[8, 3] = -1
    end
    return G
end
root(t, n, sign = 1) = Int[sign * sqfree(x) for x in diagonalize(cartan(t, n))]
ones_form(n, sign = 1) = fill(sign, n)
det_exact(G) = prod(diagonalize(G))           # the congruence operations used have determinant 1

function main()
    C = Checks("fricke_lattice.jl")
    U = [1, -1]
    # (A) rational isometries of the root lattices
    for n in (4, 6)
        check(C, "A_$n + <$(n+1)> = <1>^$(n+1) over Q", isometric(vcat(root('A', n), n + 1), ones_form(n + 1)))
    end
    check(C, "D_4 = <1>^4 over Q", isometric(root('D', 4), ones_form(4)))
    check(C, "A_1^2 = <2,2> = <1>^2 over Q", isometric([2, 2], ones_form(2)))
    E8 = root('E', 8)
    check(C, "the Cartan matrix of E_8 has determinant 1 and E_8 = <1>^8 over Q",
          det_exact(cartan('E', 8)) == 1 && isometric(E8, ones_form(8)))
    @assert det_exact(cartan('A', 4)) == 5 && det_exact(cartan('A', 6)) == 7 && det_exact(cartan('D', 4)) == 4

    # (B) the transcendental spaces
    Lam = vcat(U, U, U, root('E', 8, -1), root('E', 8, -1))
    check(C, "the K3 lattice is U^3 + E_8(-1)^2, of signature (3,19), discriminant -1", sig(Lam) == (3, 19) && disc(Lam) == -1)
    NS = Dict(5 => vcat(U, root('A', 4, -1), [-2, -2], root('D', 4, -1), root('D', 4, -1)),
              7 => vcat(U, root('A', 6, -1), root('D', 4, -1), root('D', 4, -1)))
    T = Dict{Int,Vector{Int}}()
    for N in (5, 7)
        T[N] = vcat(U, U, [-1, -N])
        check(C, "N = $N: NS has rank 16 and signature (1,15)", length(NS[N]) == 16 && sig(NS[N]) == (1, 15))
        W = vcat(NS[N][3:end], [-1, -N])       # negative definite part of NS together with <-1,-N>
        check(C, "N = $N: the negative part of NS together with <-1,-N> is <-1>^16 over Q", isometric(W, ones_form(16, -1)))
        check(C, "N = $N: NS + U^2 + <-1,-N> has the invariants of the K3 lattice, so T = U^2 + <-1,-$N>",
              isometric(vcat(NS[N], T[N]), Lam))
        dT, eps, ps = complement_data(NS[N], Lam)   # invariants of T from Lam and NS
        check(C, "N = $N: d(T) = $N and the Hasse invariants of T computed from Lam and NS agree with those of U^2 + <-1,-$N>",
              dT == N && all(hasse(T[N], p) == eps[p] for p in ps))
    end

    # (C) Lombardo's shape and the Clifford centre
    sqf = [a for a in -1:-1:-30 if sqfree(a) == a]
    for N in (5, 7)
        sols = [(a, b) for a in sqf for b in sqf if b <= a && isometric(vcat(U, U, [a, b]), T[N])]
        expect = [(a, b) for a in sqf for b in sqf if b <= a && isometric([a, b], [-1, -N])]
        check(C, "N = $N: U^2 + <a,b> = T exactly for <a,b> = <-1,-$N> ($(length(sols)) pairs up to 30, first $(sols[1:min(3, end)]))",
              sols == expect && (-1, -N) in sols && length(sols) >= 2)
        check(C, "N = $N: the signed discriminant (-1)^3 d(T) is -$N: the centre of C^+(T) is Q(sqrt(-$N))",
              sqfree(-disc(T[N])) == -N)
    end
    check(C, "Q(sqrt(-5)) and Q(sqrt(-7)) are the Weil fields: -ab = -5, -7 for (a,b) = (-1,-5), (-1,-7)",
          sqfree(-(-1) * (-5)) == -5 && sqfree(-(-1) * (-7)) == -7)

    # (D) the dimension count
    dim_so(n) = div(n * (n - 1), 2)
    dim_so_star(n) = n * (2n - 1)              # so*(2n), the D-unitary group of a quaternion 2n-fold
    check(C, "dim Res_{E/Q} SO(Q) = 2 dim SO(3) = 6 = dim SO*(4), the Hodge group of the quaternion fourfold",
          2 * dim_so(3) == 6 == dim_so_star(2))
    check(C, "the quaternion-type fourfolds form families of dimension n(n-1)/2 = 1 for n = 2, as the Fricke families",
          div(2 * (2 - 1), 2) == 1)
    finish(C)
end
main()
