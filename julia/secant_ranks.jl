# Lemmas lem:secantranks and lem:secanteuler, and the dimension count of Theorem thm:kunnethfour.
# On an abelian n-fold X, n = 3, 4, with H^1(X,C) spanned by dz_j (bit j) and dzbar_j (bit n+j), take
# h = sum_j eps_j dz_j dzbar_j, alpha = Re exp(sqrt(-q) h), beta = Im exp(sqrt(-q) h)/sqrt(q) and ch = r alpha + s beta.
# HT^1 acts by wedge with dzbar_j and contraction with d/dz_j.  Exact Rational{BigInt} arithmetic.
# (1) rank of HT^k -> H^*(X), y -> y _| ch, is 1, 2C(n,k) (0<k<n), 1 (k=n);
# (2) the forced dimensions 1, 2n, n(n-1) give chi = -2 at n = 4 and are Serre-consistent only at n = 3;
# (3) chi(ch,ch) = int tau(ch) ch equals 8q(qr^2+s^2)Pf(h) at n = 4 (Pf = +-1) and 0 at n = 3;
# (4) the ideal sheaf of a point, ch = 1 - [pt], has contraction ranks 1, 8, 12 and chi = -2.
include(joinpath(@__DIR__, "quadratic_forms.jl")); using .QuadraticForms

const QQ = Rational{BigInt}
const Form = Dict{UInt64,QQ}

prune(f::Form) = filter(p -> !iszero(p.second), f)
function addf(a::Form, b::Form, c=1)
    out = copy(a)
    for (k, v) in b; out[k] = get(out, k, zero(QQ)) + QQ(c) * v end
    prune(out)
end
scalef(a::Form, c) = prune(Form(k => QQ(c) * v for (k, v) in a))
sgn_ins(m::UInt64, i) = isodd(count_ones(m & ((UInt64(1) << i) - 1))) ? -1 : 1
function wedge1(f::Form, i)
    out = Form()
    for (m, c) in f
        (m >> i) & 1 == 1 && continue
        mm = m | (UInt64(1) << i); out[mm] = get(out, mm, zero(QQ)) + sgn_ins(m, i) * c
    end
    prune(out)
end
function iota1(f::Form, i)
    out = Form()
    for (m, c) in f
        (m >> i) & 1 == 0 && continue
        mm = m & ~(UInt64(1) << i); out[mm] = get(out, mm, zero(QQ)) + sgn_ins(mm, i) * c
    end
    prune(out)
end
function wedge(a::Form, b::Form)
    out = Form()
    for (ma, ca) in a, (mb, cb) in b
        ma & mb != 0 && continue
        s = 1; m = ma; x = mb
        while x != 0
            i = trailing_zeros(x); x &= x - 1
            isodd(count_ones(m >> (i + 1))) && (s = -s)
            m |= UInt64(1) << i
        end
        out[ma | mb] = get(out, ma | mb, zero(QQ)) + s * ca * cb
    end
    prune(out)
end
function power(h::Form, k)
    out = Form(UInt64(0) => one(QQ))
    for _ in 1:k; out = wedge(out, h) end
    out
end
hclass(n, eps) = Form((UInt64(1) << (j - 1)) | (UInt64(1) << (n + j - 1)) => QQ(eps[j]) for j in 1:n)
function secant(n, h, q)
    al = Form(); be = Form()
    for k in 0:n
        t = power(h, k); c = QQ(1, factorial(big(k))) * QQ(-q)^(k ÷ 2)
        iseven(k) ? (al = addf(al, t, c)) : (be = addf(be, t, c))
    end
    al, be
end
tau(x::Form) = Form(m => (iseven(count_ones(m) ÷ 2) ? c : -c) for (m, c) in x)
function integral(x::Form, n)
    top = (UInt64(1) << (2n)) - 1
    vol = power(hclass(n, ones(Int, n)), n)[top] / factorial(big(n))
    get(x, top, zero(QQ)) / vol
end
function rank(rows::Vector{Form})
    basis = Tuple{UInt64,Form}[]
    for r0 in rows
        r = copy(r0)
        for (p, br) in basis
            haskey(r, p) && (r = addf(r, br, -r[p] / br[p]))
        end
        isempty(r) || push!(basis, (minimum(keys(r)), r))
    end
    length(basis)
end
function subsets(N, k)
    k == 0 && return [Int[]]
    [vcat(s, [x]) for s in subsets(N, k - 1) for x in (isempty(s) ? 1 : s[end] + 1):N]
end
# operator i (1..2n): i <= n wedge with dzbar_i, i > n contraction with d/dz_{i-n}
applyop(n, i, f) = i <= n ? wedge1(f, n + i - 1) : iota1(f, i - n - 1)
function contraction_rank(n, ch::Form, k)
    rows = Form[]
    for S in subsets(2n, k)
        f = ch
        for i in reverse(S); f = applyop(n, i, f) end
        push!(rows, f)
    end
    rank(rows)
end
expected(n, k) = k == 0 ? 1 : (k == n ? 2 * binomial(n, k) - 1 : 2 * binomial(n, k))

C = Checks("secant_ranks.jl")
for n in (3, 4)
    for (q, r, s) in [(QQ(3), 1, 1), (QQ(5), 2, -3), (QQ(1, 4), 0, 1), (QQ(7, 2), 1, 0)]
        h = hclass(n, ones(Int, n)); al, be = secant(n, h, q)
        ch = addf(scalef(al, r), be, s)
        rks = [contraction_rank(n, ch, k) for k in 0:n]
        check(C, "n=$n q=$q (r,s)=($r,$s): contraction ranks $rks", rks == [expected(n, k) for k in 0:n])
    end
    e = [1, 2n, n * (n - 1)]
    if n == 3
        check(C, "n=3: forced dims 1,6,6 satisfy Serre duality e2 = e1 (2n = n(n-1))", e[2] == e[3])
    else
        check(C, "n=4: forced dims 1,8,12,8,1 give chi = -2", 2e[1] - 2e[2] + e[3] == -2)
    end
    for eps in (ones(Int, n), vcat(ones(Int, n - 1), [-1]))
        h = hclass(n, eps); Pf = integral(power(h, n), n) / factorial(big(n))
        good = true
        for (q, r, s) in [(QQ(3), 1, 1), (QQ(5), 2, -3), (QQ(1, 4), 0, 1), (QQ(2), 1, 0), (QQ(7, 3), QQ(1, 2), 5)]
            al, be = secant(n, h, q); x = addf(scalef(al, r), be, s)
            chi = integral(wedge(tau(x), x), n)
            good &= chi == (n == 4 ? 8q * (q * r^2 + s^2) * Pf : 0)
        end
        check(C, "n=$n Pf(h)=$Pf: chi = $(n == 4 ? "8q(qr^2+s^2)Pf(h)" : "0") on five secant classes", good)
    end
end
let n = 4, top = (UInt64(1) << 8) - 1
    vol = power(hclass(n, ones(Int, n)), n)[top] / 24
    chp = Form(UInt64(0) => one(QQ), top => -vol)
    rks = [contraction_rank(n, chp, k) for k in 0:2]
    check(C, "ideal of a point on a fourfold: ranks $rks, chi = $(integral(wedge(tau(chp), chp), n))",
          rks == [1, 8, 12] && integral(wedge(tau(chp), chp), n) == -2)
    # the example of the text: q = 1/4, h = e1+e2+e3-e4, beta = h - h^3/24 has chi = -2
    h = hclass(n, [1, 1, 1, -1]); al, be = secant(n, h, QQ(1, 4))
    check(C, "beta = h - h^3/24 for Pf(h) = -1, q = 1/4: chi = -2", integral(wedge(tau(be), be), n) == -2)
end
finish(C)
