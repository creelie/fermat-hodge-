# Lemma lem:secantranks for q < 0 and the Kunneth count in the proof of Theorem thm:kunnethfour.
# (1) For q = -3/4, -5/4, -1/16 (the real class (i/2) sum dz dzbar corresponds to q -> -q/4) the contraction ranks
#     of HT^k(X) into alpha + beta are those of Lemma lem:secantranks, n = 3, 4;
# (2) on X x X, n = 3, the rank of HT^2(X x X) -> H^*(X x X), xi -> xi _| (ch F_1 boxtimes ch F_2), equals
#     sum_{a+b=2} rk_a rk_b = 1*6 + 6*6 + 6*1 = 48.  Exact Rational{BigInt} arithmetic.
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

# a form on X (2n generators) placed on the first, resp. second, factor of X x X (4n generators:
# dz_0..dz_{2n-1}, dzbar_0..dzbar_{2n-1})
function embed(f::Form, n, second::Bool)
    out = Form()
    for (m, c) in f
        mm = UInt64(0)
        for i in 0:(2n - 1)
            (m >> i) & 1 == 1 || continue
            j = i < n ? i : i + n
            second && (j += n)
            mm |= UInt64(1) << j
        end
        out[mm] = c
    end
    out
end

C = Checks("kunneth_rank.jl")
for n in (3, 4), q in (QQ(-3, 4), QQ(-5, 4), QQ(-1, 16))
    h = hclass(n, ones(Int, n)); al, be = secant(n, h, q)
    rks = [contraction_rank(n, addf(al, be), k) for k in 0:n]
    check(C, "n=$n q=$q: contraction ranks $rks", rks == [expected(n, k) for k in 0:n])
end
let n = 3
    h = hclass(n, ones(Int, n))
    al, be = secant(n, h, QQ(3)); ch1 = addf(al, be); ch2 = addf(scalef(al, 2), be, -1)
    big = wedge(embed(ch1, n, false), embed(ch2, n, true))
    rk2 = contraction_rank(2n, big, 2)
    a = [expected(n, k) for k in 0:2]
    check(C, "n=3: rank of HT^2(X x X) into ch F_1 x ch F_2 is $rk2 = sum rk_a rk_b", rk2 == a[3] * a[1] + a[2]^2 + a[1] * a[3])
end
finish(C)
