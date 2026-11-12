# annihilator_exact.jl -- port of code/annihilator_exact.py.
# Exact arithmetic over Q(sqrt(-3)) in the exterior-algebra model of
# H^*(A x A') at (m,m') = (2,1) and (2,2):
#   (1) dim T D_{n,n} = n^2, dim T(product locus) = m^2 + m'^2, mixed = 2mm';
#   (2) ch(E') = M w + sum_i (M/N_i) p_i(theta_A) (x) (sum_j a_ij omega'_j);
#   (3) the annihilator of ch(E') in T D_{n,n} has dimension m^2 + m'^2;
#   (4) the same for each component theta_A^k (x) R_k, k >= 1;
#   (5) the annihilators of theta_A^k (x) theta'^b in T D_{n,n}.
# Monomials of the exterior algebra on 4n generators are bit masks
# (generator e_j -> bit 2j, f_j -> bit 2j+1); all ranks are exact.
# Run: julia --startup-file=no annihilator_exact.jl

const QQ = Rational{BigInt}
const DD = 3
struct K
    a::QQ
    b::QQ
end
K(a::Integer) = K(QQ(a), QQ(0))
K(a::Integer, b::Integer) = K(QQ(a), QQ(b))
Base.:+(s::K, o::K) = K(s.a + o.a, s.b + o.b)
Base.:-(s::K, o::K) = K(s.a - o.a, s.b - o.b)
Base.:-(s::K) = K(-s.a, -s.b)
Base.:*(s::K, o::K) = K(s.a * o.a - DD * s.b * o.b, s.a * o.b + s.b * o.a)
Base.conj(s::K) = K(s.a, -s.b)
nrm(s::K) = s.a * s.a + DD * s.b * s.b
Base.inv(s::K) = (n = nrm(s); K(s.a / n, -s.b / n))
Base.:/(s::K, o::K) = s * inv(o)
Base.iszero(s::K) = iszero(s.a) && iszero(s.b)
Base.:(==)(s::K, o::K) = s.a == o.a && s.b == o.b
const ONE = K(1); const ZERO = K(0); const RT = K(0, 1)

const Elt = Dict{UInt32,K}
bit(g) = UInt32(1) << g
gen(g) = Elt(bit(g) => ONE)
e_(j) = gen(2j); f_(j) = gen(2j + 1)
clean!(r::Elt) = (filter!(p -> !iszero(p.second), r); r)
function add(a::Elt, b::Elt, cb::K=ONE)
    r = copy(a)
    for (k, v) in b
        r[k] = get(r, k, ZERO) + cb * v
    end
    clean!(r)
end
scal(a::Elt, c::K) = Elt(k => c * v for (k, v) in a)
function wedge(a::Elt, b::Elt)
    r = Elt()
    for (ka, va) in a, (kb, vb) in b
        ka & kb != 0 && continue
        s = 0; t = kb
        while t != 0
            y = trailing_zeros(t); t &= t - UInt32(1)
            s += count_ones(ka >> (y + 1))
        end
        v = va * vb
        isodd(s) && (v = -v)
        k = ka | kb
        r[k] = get(r, k, ZERO) + v
    end
    clean!(r)
end
function contract(g::Int, a::Elt)
    r = Elt(); bg = bit(g)
    for (k, v) in a
        k & bg == 0 && continue
        pos = count_ones(k & (bg - UInt32(1)))
        r[k ⊻ bg] = isodd(pos) ? -v : v
    end
    r
end
wedge_gen(g::Int, a::Elt) = wedge(gen(g), a)
function power(a::Elt, k::Int)
    r = Elt(UInt32(0) => ONE)
    for _ in 1:k
        r = wedge(r, a)
    end
    r
end

"exact rank of a list of sparse rows (Gaussian elimination over Q(sqrt(-3)))"
function rank_exact(rows0::Vector{Dict{UInt64,K}})
    rows = [copy(r) for r in rows0 if !isempty(r)]
    rk = 0
    while !isempty(rows)
        piv = pop!(rows)
        isempty(piv) && continue
        rk += 1
        c = minimum(keys(piv)); pc = piv[c]
        new = Dict{UInt64,K}[]
        for r in rows
            if haskey(r, c)
                f = r[c] / pc
                for (k, v) in piv
                    r[k] = get(r, k, ZERO) - f * v
                end
                filter!(p -> !iszero(p.second), r)
            end
            isempty(r) || push!(new, r)
        end
        rows = new
    end
    rk
end

function ops(n)
    w = vcat([2j + 1 for j in 0:n-1], [2j for j in n:2n-1])   # H^{0,1}
    c = vcat([2j for j in 0:n-1], [2j + 1 for j in n:2n-1])   # T = (H^{1,0})^*
    w, c
end
h1T_ops(n) = ((w, c) = ops(n); [(a, v) for a in w for v in c])
apply_op(op, a::Elt) = wedge_gen(op[1], contract(op[2], a))
function ann_dim(gammas::Vector{Elt}, op_list)
    rows = Dict{UInt64,K}[]
    for o in op_list
        row = Dict{UInt64,K}()
        for (t, g) in enumerate(gammas), (k, v) in apply_op(o, g)
            row[(UInt64(t) << 32) | k] = v
        end
        push!(rows, row)
    end
    length(op_list) - rank_exact(rows)
end

const NPASS = Ref(0); const NFAIL = Ref(0)
function check(name, ok)
    ok ? (NPASS[] += 1) : (NFAIL[] += 1)
    println(ok ? "PASS " : "FAIL ", name)
end

function run(n, m)
    mp = n - m
    tag = "n=$n (m,m')=($m,$mp)"
    IA = vcat(0:m-1, n:n+m-1); IB = [j for j in 0:2n-1 if !(j in IA)]
    # theta = i sum s_j e_j f_j; the factor i is dropped (irrelevant for the ranks)
    function theta(I)
        t = Elt()
        for j in I
            t = add(t, wedge(e_(j), f_(j)), j < n ? ONE : -ONE)
        end
        t
    end
    function om(I, plus)
        r = Elt(UInt32(0) => ONE)
        for j in I
            r = wedge(r, plus ? e_(j) : f_(j))
        end
        r
    end
    thA, thB = theta(IA), theta(IB); th = add(thA, thB)
    opA, omA, opB, omB = om(IA, true), om(IA, false), om(IB, true), om(IB, false)
    H1T = h1T_ops(n)
    blockA = [o for o in H1T if (o[1] ÷ 2 in IA) && (o[2] ÷ 2 in IA)]
    blockB = [o for o in H1T if (o[1] ÷ 2 in IB) && (o[2] ÷ 2 in IB)]
    Wp = wedge(opA, opB); Wm = wedge(omA, omB)
    TD = ann_dim([th, Wp, Wm], H1T)
    TA = ann_dim([thA, opA, omA], blockA); TB = ann_dim([thB, opB, omB], blockB)
    println("=== $tag, field Q(sqrt(-$DD)): dim T D = $TD, dim T(product locus) = $TA+$TB, mixed = $(TD-TA-TB) ===")
    check("$tag (1) dim T D_(n,n) = n^2 = $(n*n)", TD == n * n)
    check("$tag (1) dim T(product locus) = m^2+m'^2 = $(m*m+mp*mp)", TA + TB == m * m + mp * mp)
    check("$tag (1) mixed directions = 2mm' = $(2m*mp)", TD - TA - TB == 2m * mp)
    weil(opl, oml, uu) = (add(scal(opl, uu), scal(oml, conj(uu))),
                          add(scal(opl, RT * uu), scal(oml, conj(RT * uu))))
    u = K(2, 1); up = K(1, -3)
    wA = weil(opA, omA, u); wB = weil(opB, omB, up)
    cA = [[1, 2, -1, 3, 1], [2, -1, 1, 1, -2]]; cB = [[1, 1, 3, -2, 1], [3, 2, -1, 1, 1]]
    pA = [Elt(), Elt()]; pB = [Elt(), Elt()]
    for i in 1:2
        for k in 0:2m
            pA[i] = add(pA[i], power(thA, k), K(cA[i][k+1]))
        end
        for k in 0:2mp
            pB[i] = add(pB[i], power(thB, k), K(cB[i][k+1]))
        end
    end
    N = [K(1), K(1)]; Np = [K(1), K(1)]
    chF = [add(scal(wA[i], N[i]), pA[i]) for i in 1:2]
    chG = [add(scal(wB[j], Np[j]), pB[j]) for j in 1:2]
    inv2(a, b, c, d) = (det = a * d - b * c; (d / det, -b / det, -c / det, a / det))
    iA = inv2(u, conj(u), RT * u, conj(RT * u))
    iB = inv2(up, conj(up), RT * up, conj(RT * up))
    x = K(1, 1)
    PA = (iA[1], iA[2]); MA = (iA[3], iA[4]); PB = (iB[1], iB[2]); MB = (iB[3], iB[4])
    a = Dict((i, j) => x * PA[i] * PB[j] + conj(x) * MA[i] * MB[j] for i in 1:2 for j in 1:2)
    w = add(scal(Wp, x), scal(Wm, conj(x)))
    chk = Elt()
    for i in 1:2, j in 1:2
        chk = add(chk, wedge(wA[i], wB[j]), a[(i, j)])
    end
    check("$tag sum a_ij omega_i (x) omega'_j = w", isempty(add(chk, w, -ONE)))
    check("$tag a_ij rational", all(iszero(v.b) for v in values(a)))
    check("$tag a = (-1/98, 2/49, 2/49, 1/294)",
          [a[(1, 1)].a, a[(1, 2)].a, a[(2, 1)].a, a[(2, 2)].a] == [-1 // 98, 2 // 49, 2 // 49, 1 // 294])
    M = K(1)
    chEp = Elt()
    for i in 1:2, j in 1:2
        chEp = add(chEp, wedge(chF[i], chG[j]), M * a[(i, j)] / (N[i] * Np[j]))
    end
    for i in 1:2
        qpi = Elt()
        for j in 1:2
            qpi = add(qpi, pB[j], a[(i, j)] / Np[j])
        end
        chEp = add(chEp, wedge(chF[i], qpi), -M / N[i])
    end
    pred = scal(w, M)
    for i in 1:2
        Rw = Elt()
        for j in 1:2
            Rw = add(Rw, wB[j], a[(i, j)])
        end
        pred = add(pred, wedge(pA[i], Rw), M / N[i])
    end
    check("$tag (2) ch(E') = M w + sum_i (M/N_i) p_i (x) sum_j a_ij omega'_j (exact)", isempty(add(chEp, pred, -ONE)))
    annEp = ann_dim([th, Wp, Wm, chEp], H1T)
    check("$tag (3) dim(T D cap Ann ch E') = $annEp = m^2+m'^2, excess 2mm'",
          annEp == TA + TB && TD - annEp == 2m * mp)
    for k in 1:2m
        Rk = Elt()
        for i in 1:2, j in 1:2
            Rk = add(Rk, wB[j], (M / N[i]) * K(cA[i][k+1]) * a[(i, j)])
        end
        comp = wedge(power(thA, k), Rk)
        d = ann_dim([th, Wp, Wm, comp], H1T)
        check("$tag (4) k=$k: dim(T D cap Ann(theta_A^$k (x) R_$k)) = $d = m^2+m'^2, R_k != 0",
              !isempty(Rk) && d == TA + TB)
    end
    for (k, b) in [(1, 0), (1, 1), (2, 1), (1, 2), (3, 0)]
        comp = wedge(power(thA, k), power(thB, b))
        d = ann_dim([th, Wp, Wm, comp], H1T)
        check("$tag (5) theta_A^$k (x) theta'^$b: dim(T D cap Ann) = $d = m^2+m'^2", d == TA + TB)
    end
end

run(3, 2); run(4, 2)
println("annihilator_exact.jl: $(NPASS[]) checks passed, $(NFAIL[]) failed")
NFAIL[] > 0 && exit(1)
