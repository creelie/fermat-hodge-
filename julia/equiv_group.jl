# equiv_group.jl -- the group G of Proposition w:prop-equivgroup.
# A = prod_j B_j, B_j = C^2/Z[i]^2.  The pieces of the line-bundle convolutions
# on E_0^(2n) have hermitian forms L_zeta = [[p, z], [conj z, p]] (z a unit of
# Z[i]) and M_i = t_i I on each factor.  g_a = t_a^*(-) (x) P_{-phi_{L_1}(a)}
# fixes L iff phi_{L-L_1}(a) = 0 iff Im(a^* F l) is integral for all l in
# Z[i]^2 (F = L - L_1).  We search the 8-torsion points a, and check:
# G_j = Z/2 exactly when all t_i - p are odd (and G_j = 0 otherwise); G is
# isotropic for the commutator pairings of L_1 and of every L_zeta - L_zeta';
# for pieces differing in k coordinates, |G_S| = 2^k divides D(zeta,zeta').
# Run: julia --startup-file=no equiv_group.jl
include(joinpath(@__DIR__, "quadratic_forms.jl"))
using .QuadraticForms

const Q = Rational{Int}
const MU4 = [(1, 0), (0, 1), (-1, 0), (0, -1)]
cmul(x, y) = (x[1] * y[1] - x[2] * y[2], x[1] * y[2] + x[2] * y[1])
cconj(x) = (x[1], -x[2])
function herm_im(F, a, b)
    s = (Q(0), Q(0))
    for r in 1:2, c in 1:2
        t = cmul(cmul(cconj(a[r]), F[r][c]), b[c]); s = (s[1] + t[1], s[2] + t[2])
    end
    return s[2]
end
const UNIT = [((1, 0), (0, 0)), ((0, 1), (0, 0)), ((0, 0), (1, 0)), ((0, 0), (0, 1))]
kills(F, a) = all(denominator(herm_im(F, a, l)) == 1 for l in UNIT)
form_L(p, z) = [[(p, 0), z], [cconj(z), (p, 0)]]
form_sc(t) = [[(t, 0), (0, 0)], [(0, 0), (t, 0)]]
sub(F, G) = [[(F[r][c][1] - G[r][c][1], F[r][c][2] - G[r][c][2]) for c in 1:2] for r in 1:2]
const N = 8
const PTS = [((Q(u, N), Q(v, N)), (Q(w, N), Q(x, N))) for u in 0:N-1 for v in 0:N-1 for w in 0:N-1 for x in 0:N-1]

function surface_group(p, ts)
    forms = vcat([form_L(p, z) for z in MU4], [form_sc(t) for t in ts])
    L1 = forms[1]
    diffs = [sub(F, L1) for F in forms]
    return [a for a in PTS if all(kills(D, a) for D in diffs)], L1
end

function main()
    C = Checks("equiv_group.jl")
    allok = true
    for (n, p, ts, expect) in [(3, 0, (2, 5, 6), 1), (3, 0, (3, 5, 7), 2), (3, 0, (-3, 3, 5), 2), (3, 1, (3, 5, 7), 1),
                               (3, 1, (-2, 4, 6), 2), (4, 0, (3, 5, 7), 2), (4, 0, (2, 4, 6), 1), (4, 0, (2, 5, 6), 1)]
        Gj, L1 = surface_group(p, ts)
        iso1 = all(denominator(herm_im(L1, a, b)) == 1 for a in Gj, b in Gj)
        isoM = all(denominator(herm_im(sub(form_L(p, z2), form_L(p, z1)), a, b)) == 1
                   for z1 in MU4, z2 in MU4, a in Gj, b in Gj)
        div_ok = true
        for k in 1:n
            for zs in Iterators.product(ntuple(_ -> MU4, k)...), zs2 in Iterators.product(ntuple(_ -> MU4, k)...)
                any(zs[i] == zs2[i] for i in 1:k) && continue
                D = prod((zs[i][1] - zs2[i][1])^2 + (zs[i][2] - zs2[i][2])^2 for i in 1:k)
                div_ok &= D % length(Gj)^k == 0
            end
        end
        pred = (length(Gj) == 2) == all(isodd(t - p) for t in ts)
        ok = length(Gj) == expect && iso1 && isoM && div_ok && pred
        check(C, "n=$n p=$p t=$ts: |G_j| = $(length(Gj)), |G| = $(length(Gj)^n); G_j = Z/2 iff all t_i - p odd; isotropic for E_L1 and all E_{L_z - L_z'}; |G_S| divides D", ok)
    end
    finish(C)
end
main()
