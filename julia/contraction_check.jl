# Exact checks on A = E_0^{2n}, n = 3, 4, for the deformation v_0 and the rank r_0
# (Lemma w:lem-vzero, Theorem w:thm-uniformexclusion).
# Exterior algebra over Q(i) on dz_0..dz_{2n-1} (bits 0..2n-1) and dzbar_0..dzbar_{2n-1} (bits 2n..4n-1);
# a form is a Dict{UInt32,CQ} from monomial bitmask to coefficient.
# (0) the Weil identity sum_zeta prod(zeta) exp(c1 L_zeta) = 2*4^(n-1)(alpha + alphabar);
# (1) T D = {K-linear v : v _| theta = 0} has dimension n^2, and v_0 lies in it;
# (2) v_0 _| c1(L_zeta) != 0 for every zeta, v_0 _| c1(M_i) = 0;
# (3) for every zeta the map T D -> H^{0,2}, v -> v _| c1(L_zeta), has the printed rank (nonzero);
# (4) r_0 = rank of HT^2 -> H^*(A), xi -> xi _| gamma, equals 7n^2-2n (57, 104), and T D lies in its kernel.
include(joinpath(@__DIR__, "quadratic_forms.jl")); using .QuadraticForms

const CQ = Complex{Rational{BigInt}}
const Form = Dict{UInt32,CQ}

function addto!(h::Form, g::Form, c::CQ=one(CQ))
    for (k, v) in g
        w = get(h, k, zero(CQ)) + c * v
        if iszero(w); delete!(h, k) else h[k] = w end
    end
    h
end
addf(f, g, c=one(CQ)) = addto!(copy(f), g, c)
scalef(f::Form, c) = Form(k => CQ(c) * v for (k, v) in f)

function wsign(a::UInt32, b::UInt32)
    s = 0; bb = b
    while bb != 0
        j = trailing_zeros(bb); bb &= bb - one(UInt32)
        s += count_ones(a >> (j + 1))
    end
    isodd(s) ? -1 : 1
end
function wedge(f::Form, g::Form)
    h = Form()
    for (ka, va) in f, (kb, vb) in g
        (ka & kb) != 0 && continue
        c = wsign(ka, kb) * (va * vb)
        k = ka | kb
        w = get(h, k, zero(CQ)) + c
        if iszero(w); delete!(h, k) else h[k] = w end
    end
    h
end
function iota(idx::Int, f::Form)     # interior product with the dual of generator idx, from the left
    h = Form(); bit = UInt32(1) << idx
    for (k, v) in f
        (k & bit) == 0 && continue
        below = count_ones(k & (bit - one(UInt32)))
        kk = k & ~bit
        c = isodd(below) ? -v : v
        w = get(h, kk, zero(CQ)) + c
        if iszero(w); delete!(h, kk) else h[kk] = w end
    end
    h
end
mono(idx...) = reduce(|, (UInt32(1) << i for i in idx); init=UInt32(0))
gen(i) = Form(mono(i) => one(CQ))
two(x, y, c) = wedge(Form(mono(x) => CQ(c)), gen(y))

function rankof(vecs::Vector{Form})
    rows = [copy(v) for v in vecs]; m = length(rows); r = 0; used = falses(m)
    cols = sort!(collect(Set(k for v in vecs for k in keys(v))))
    for col in cols
        piv = findfirst(i -> !used[i] && haskey(rows[i], col), 1:m)
        piv === nothing && continue
        used[piv] = true; r += 1
        inv = 1 / rows[piv][col]
        for i in 1:m
            if i != piv && haskey(rows[i], col)
                addto!(rows[i], rows[piv], -rows[i][col] * inv)
            end
        end
    end
    r
end
function nullspace(vecs::Vector{Form})
    rows = [copy(v) for v in vecs]; m = length(rows)
    tags = [Form(UInt32(i) => one(CQ)) for i in 1:m]     # tag keys are just labels
    used = falses(m)
    for col in sort!(collect(Set(k for v in vecs for k in keys(v))))
        piv = findfirst(i -> !used[i] && haskey(rows[i], col), 1:m)
        piv === nothing && continue
        used[piv] = true
        inv = 1 / rows[piv][col]
        for i in 1:m
            if i != piv && haskey(rows[i], col)
                f = -rows[i][col] * inv
                addto!(rows[i], rows[piv], f); addto!(tags[i], tags[piv], f)
            end
        end
    end
    [[get(tags[i], UInt32(j), zero(CQ)) for j in 1:m] for i in 1:m if isempty(rows[i])]
end

function run(C, n, p, t, sig)
    dz(j) = j; dzb(j) = 2n + j
    hi = CQ(0, 1 // 2)
    a  = [two(dz(j), dzb(j), hi) for j in 0:n-1]
    b  = [two(dz(n + j), dzb(n + j), hi) for j in 0:n-1]
    c  = [two(dz(j), dzb(n + j), hi) for j in 0:n-1]
    cp = [two(dz(n + j), dzb(j), hi) for j in 0:n-1]
    theta = Form(); for j in 1:n; addto!(theta, a[j]); addto!(theta, b[j]) end
    function c1L(z)
        f = Form()
        for j in 1:n
            addto!(f, a[j], CQ(p)); addto!(f, b[j], CQ(p))
            addto!(f, c[j], z[j]); addto!(f, cp[j], conj(z[j]))
        end
        f
    end
    contract_v(v, f) = reduce((h, kv) -> addto!(h, wedge(gen(dzb(kv[1][1])), iota(dz(kv[1][2]), f)), kv[2]), v; init=Form())
    Klin = vcat([(n + bb, aa) for aa in 0:n-1 for bb in 0:n-1], [(bb, n + aa) for aa in 0:n-1 for bb in 0:n-1])
    rows = [contract_v([(key, one(CQ))], theta) for key in Klin]
    kern = nullspace(rows)
    TD = [[(Klin[i], co) for (i, co) in enumerate(vec) if !iszero(co)] for vec in kern]
    v0 = [((n + 1, 0), one(CQ)), ((0, n + 1), one(CQ))]
    mu4 = [CQ(1), CQ(0, 1), CQ(-1), CQ(0, -1)]
    zetas = [collect(z) for z in Iterators.product(ntuple(_ -> mu4, n)...) if prod(z) in (CQ(1), CQ(-1))]
    allnz = all(z -> !isempty(contract_v(v0, c1L(z))), zetas)
    ranks = Set(rankof([contract_v(v, c1L(z)) for v in TD]) for z in zetas)
    okM = all(tt -> isempty(contract_v(v0, scalef(theta, tt))), t)
    function expo(f)
        res = Form(UInt32(0) => one(CQ)); term = Form(UInt32(0) => one(CQ))
        for k in 1:2n
            term = scalef(wedge(term, f), 1 // k); addto!(res, term)
        end
        res
    end
    alpha = reduce(wedge, c; init=Form(UInt32(0) => one(CQ)))
    alphab = reduce(wedge, cp; init=Form(UInt32(0) => one(CQ)))
    gamma = scalef(addf(alpha, alphab), 2 * 4^(n - 1))
    for (tt, s) in zip(t, sig); addto!(gamma, expo(scalef(theta, tt)), CQ(s)) end
    S = Form()
    for z in zetas; addto!(S, expo(c1L(z)), prod(z) == CQ(1) ? CQ(1) : CQ(-1)) end
    weil = isempty(addf(S, addf(alpha, alphab), CQ(-2 * 4^(n - 1))))
    HT = Tuple{Symbol,Int,Int}[]
    for x in 0:2n-1, y in x+1:2n-1; push!(HT, (:y, x, y)) end
    for bb in 0:2n-1, aa in 0:2n-1; push!(HT, (:v, bb, aa)) end
    for x in 0:2n-1, y in x+1:2n-1; push!(HT, (:w, x, y)) end
    function contract_xi(xi, f)
        kind, x, y = xi
        kind == :y && return wedge(wedge(gen(dzb(x)), gen(dzb(y))), f)
        kind == :v && return wedge(gen(dzb(x)), iota(dz(y), f))
        return iota(dz(x), iota(dz(y), f))
    end
    r0 = rankof([contract_xi(xi, gamma) for xi in HT])
    TDin = all(v -> isempty(contract_v(v, gamma)), TD)
    println("n=$n: dim TD=$(length(TD)), ranks=$(sort(collect(ranks))), r0=$r0 on HT^2 of dim $(length(HT))")
    check(C, "n=$n Weil identity", weil)
    check(C, "n=$n dim TD = n^2 and v0 _| theta = 0", length(TD) == n^2 && isempty(contract_v(v0, theta)))
    check(C, "n=$n v0 _| c1(L_zeta) != 0 for all $(length(zetas)) zeta, v0 _| c1(M_i) = 0", allnz && okM)
    check(C, "n=$n rank of TD -> H^{0,2} is $(n == 3 ? 3 : 6) for every zeta", ranks == Set([n == 3 ? 3 : 6]))
    check(C, "n=$n r0 = 7n^2-2n and TD in kernel", r0 == 7n^2 - 2n && TDin)
end

C = Checks("contraction_check.jl")
run(C, 3, 0, (3, 5, 7), (1, -1, 1))
run(C, 4, 0, (3, 5, 7), (1, -1, 1))
finish(C)
