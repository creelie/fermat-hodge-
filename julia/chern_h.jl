# The Chern character of a convolution of line bundles and threefold pieces at E_0^6 against theta_h.
# Julia port of the round program chern_h.py (nine checks).
#
# Part A (weight-zero algebra).  R0 = Q[a1,a2,a3,b1,b2,b3]/(a_j^2, b_j^2): theta = sum(a_j + b_j),
# theta_h = sum(h_j a_j + h_{3+j} b_j), X0 = prod(a_j + b_j) = weight-zero part of every [Z_zeta].
# The weight-zero part of ch(E) in degree 2k is P_k theta^k + R_{k-3} X0 theta^(k-3) (pieces O_Z L^k and
# L^l with L of class theta), and the polarised shape w.r.t. theta_h asks it to be c_k theta_h^k.
# For all h in {1,2,3}^6: a solution with c_k != 0 exists for some k in 1..5  <=>  h is constant.
# With L replaced by L_h of class theta_h: is X0 theta_h^(k-3) proportional to theta_h^k ?
#
# Part B (contraction ranks).  Exterior algebra on dz_1..dz_6, dzbar_1..dzbar_6;
# HT^2 = H^2(O) + H^1(T) + H^0(L^2 T) acts by wedge, derivation, double interior product.
# r(gamma) = rank of xi -> xi . gamma, and the first-order Hodge locus = kernel on H^1(T).
#
#   julia --startup-file=no chern_h.jl
#
# Exact arithmetic over Q (Rational{BigInt}); no packages.

module ChernH

const Q = Rational{BigInt}
const Vec = Dict{Int,Q}                 # sparse vector: monomial (bit mask) -> coefficient

npass = 0; nfail = 0
function check(name, ok)
    global npass, nfail
    println(ok ? "PASS " : "FAIL ", name)
    ok ? (npass += 1) : (nfail += 1)
end

clean!(r::Vec) = filter!(p -> p.second != 0, r)

# ------------------------------------------------------------------ Part A
function pmul(p::Vec, q::Vec)           # product in R0: squares of the variables vanish
    r = Vec()
    for (m1, c1) in p, (m2, c2) in q
        m1 & m2 != 0 && continue
        r[m1|m2] = get(r, m1 | m2, Q(0)) + c1 * c2
    end
    return clean!(r)
end
function ppow(p::Vec, k::Int)
    r = Vec(0 => Q(1))
    for _ in 1:k
        r = pmul(r, p)
    end
    return r
end
lin(coeffs) = Vec(1 << (i - 1) => Q(c) for (i, c) in enumerate(coeffs))     # a1,a2,a3,b1,b2,b3 -> bits 0..5

"rank of a list of sparse vectors, by elimination over Q"
function rank(rows::Vector{Vec})
    rows = [copy(r) for r in rows]
    rk = 0
    while !isempty(rows)
        r = pop!(rows)
        isempty(r) && continue
        piv = minimum(keys(r)); pc = r[piv]; rk += 1
        for s in rows
            if haskey(s, piv)
                f = s[piv] / pc
                for (m, c) in r
                    s[m] = get(s, m, Q(0)) - f * c
                end
                clean!(s)
            end
        end
    end
    return rk
end
in_span(target::Vec, gens::Vector{Vec}) = rank(vcat(gens, [target])) == rank(gens)

# ------------------------------------------------------------------ Part B
# generators: dz_1..dz_6 = bits 0..5, dzbar_1..dzbar_6 = bits 6..11; sign by the order of the bits
function wedge1(g::Int, f::Vec)         # dx_g ^ f
    r = Vec()
    for (m, c) in f
        (m >> g) & 1 == 1 && continue
        s = count_ones(m & ((1 << g) - 1))
        r[m|(1<<g)] = get(r, m | (1 << g), Q(0)) + (iseven(s) ? c : -c)
    end
    return r
end
function inter(g::Int, f::Vec)          # interior product with the dual vector of the generator g
    r = Vec()
    for (m, c) in f
        (m >> g) & 1 == 0 && continue
        s = count_ones(m & ((1 << g) - 1))
        r[m⊻(1<<g)] = get(r, m ⊻ (1 << g), Q(0)) + (iseven(s) ? c : -c)
    end
    return r
end
function wedge(f::Vec, g::Vec)
    r = Vec()
    for (m1, c1) in f, (m2, c2) in g
        m1 & m2 != 0 && continue
        s = 0                           # number of generators of m1 greater than each generator of m2
        for b in 0:11
            (m2 >> b) & 1 == 1 && (s += count_ones(m1 >> (b + 1)))
        end
        r[m1|m2] = get(r, m1 | m2, Q(0)) + (iseven(s) ? c1 * c2 : -c1 * c2)
    end
    return clean!(r)
end
function addf(f::Vec, g::Vec, cg=Q(1))
    r = copy(f)
    for (m, c) in g
        r[m] = get(r, m, Q(0)) + cg * c
    end
    return clean!(r)
end
const ONE = Vec(0 => Q(1))
function form(gens)
    f = ONE
    for g in reverse(gens)
        f = wedge1(g, f)
    end
    return f
end

function main()
    # ---------------- Part A
    theta = lin([1, 1, 1, 1, 1, 1])
    X0 = Vec(0 => Q(1))
    for j in 0:2
        X0 = pmul(X0, Vec(1 << j => Q(1), 1 << (3 + j) => Q(1)))
    end
    thetapow = [ppow(theta, k) for k in 0:6]
    bad_L = 0; bad_Lh = Tuple{NTuple{6,Int},Int}[]
    n_const = 0; n_nonconst = 0
    for h1 in 1:3, h2 in 1:3, h3 in 1:3, h4 in 1:3, h5 in 1:3, h6 in 1:3
        h = (h1, h2, h3, h4, h5, h6)
        th = lin(h)
        isconst = length(unique(h)) == 1
        isconst ? (n_const += 1) : (n_nonconst += 1)
        some = false
        for k in 1:5
            gens = k >= 3 ? [thetapow[k+1], pmul(X0, thetapow[k-2])] : [thetapow[k+1]]
            some |= in_span(ppow(th, k), gens)
        end
        some != isconst && (bad_L += 1)
        # with L_h: is X0 theta_h^(k-3) a multiple of theta_h^k ?  (then R may be nonzero)
        for k in (3, 4, 5)
            dep = in_span(pmul(X0, ppow(th, k - 3)), [ppow(th, k)])
            expect = (k == 5 && all(h[j] == h[3+j] for j in 1:3))
            dep != expect && push!(bad_Lh, (h, k))
        end
    end
    check("A1: over $(n_const + n_nonconst) values of h in {1,2,3}^6, 'c_k != 0 possible for some 1<=k<=5 with pieces " *
          "O_Z L^k, L^l, class(L)=theta' holds exactly for the $n_const constant h",
          bad_L == 0 && n_const == 3 && n_nonconst == 726)
    check("A2: with L_h in place of L: X0 theta_h^(k-3) is proportional to theta_h^k only for k=5 and h_j = h_{3+j} " *
          "(k=3,4: never), so Q = sum(-1)^s = 0 and sum(-1)^s k = 0 are forced for every h", isempty(bad_Lh))
    t5 = thetapow[6]; x2 = pmul(X0, thetapow[3]); t6 = thetapow[7]; x3 = pmul(X0, thetapow[4])
    check("A3: X0 theta^2 = theta^5/15 and X0 theta^3 = theta^6/15 (h = 1)",
          all(get(x2, m, Q(0)) * 15 == c for (m, c) in t5) && length(x2) == length(t5) &&
          all(get(x3, m, Q(0)) * 15 == c for (m, c) in t6))
    check("A4: X0 theta is not a multiple of theta^4, X0 not a multiple of theta^3 (h = 1)",
          !in_span(pmul(X0, theta), [thetapow[5]]) && !in_span(X0, [thetapow[4]]))

    # ---------------- Part B
    thp = Vec()                       # theta' = sum dz_j ^ dzbar_j  (theta = (i/2) theta')
    for j in 0:5
        thp = addf(thp, wedge1(j, wedge1(6 + j, ONE)))
    end
    alpha = form([0, 1, 2, 9, 10, 11])          # dz1 dz2 dz3 dzbar4 dzbar5 dzbar6
    alphabar = form([6, 7, 8, 3, 4, 5])
    omega = addf(alpha, alphabar)
    TP = [ONE]
    for _ in 1:6
        push!(TP, wedge(TP[end], thp))
    end
    check("B0: omega theta' = 0", isempty(wedge(omega, thp)))

    function stats(gamma)
        H2O = [wedge1(6 + k, wedge1(6 + l, gamma)) for k in 0:5 for l in k+1:5]
        H1T = [wedge1(6 + k, inter(l, gamma)) for k in 0:5 for l in 0:5]
        L2T = [inter(k, inter(l, gamma)) for k in 0:5 for l in k+1:5]
        return rank(vcat(H2O, H1T, L2T)), 36 - rank(H1T)
    end
    function gam(cs)
        g = copy(omega)
        for (k, c) in enumerate(cs)
            c != 0 && (g = addf(g, TP[k], Q(c)))
        end
        return g
    end
    # generic polarised class: polynomial part the sum of three exponentials e^{theta'}, e^{2 theta'}, e^{3 theta'}
    cs = [Q(1 + 2 * big(2)^k + 5 * big(3)^k) / factorial(big(k)) for k in 0:6]
    r, loc = stats(gam(cs))
    check("B1: three exponentials (Hankel rank 3): r = $r (expected 57), first-order Hodge locus $loc (expected 9)", (r, loc) == (57, 9))
    r, loc = stats(gam([1, 0, 0, 0, 0, 0, 1]))
    check("B2: gamma = omega + c0 + c6 theta^6: r = $r (expected 48), locus $loc (expected 18)", (r, loc) == (48, 18))
    r, loc = stats(gam([0, 0, 0, 0, 0, 0, 1]))
    check("B3: gamma = omega + c6 theta^6: r = $r (expected 39), locus $loc (expected 18)", (r, loc) == (39, 18))
    r, loc = stats(gam([0, 0, 0, 0, 0, 0, 0]))
    check("B4: gamma = omega: r = $r (expected 30), locus $loc (expected 18)", (r, loc) == (30, 18))

    println("chern_h.jl: $npass checks passed, $nfail failed")
    return nfail
end

end # module

if abspath(PROGRAM_FILE) == @__FILE__
    exit(ChernH.main() > 0 ? 1 : 0)
end
