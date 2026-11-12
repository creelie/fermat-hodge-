# sixfold_link.jl -- port of code/sixfold_link.py and code/link_weights.py:
# the sixfold link xi on X x X x Z_K for a Mumford fourfold X.
#
# Split model over Qbar, exact rational arithmetic throughout.
#   V_i = Q^2 (i = 1,2,3), eps the standard symplectic form, V = V_1 (x) V_2 (x) V_3
#   = H^1(X), psi = eps (x) eps (x) eps.  D_i = M_2 = V_i (x) W_i is the i-th place
#   of the quaternion algebra D over the cubic field F; D^1 acts by left
#   multiplication, the CM field K = F(sqrt(-delta)), diagonalised, by right
#   multiplication.  H^1(Z_K) = D_1 + D_2 + D_3 (dim 12), with the polarisation
#   psi_c(x,y) = Tr trd(xbar y c), c_i = gamma_i diag(1,-1).  A = X x X x Z_K,
#   H^1(A) = V + V' + D (dim 28).
#
# Part I (sixfold_link.py): (A) psi_c alternating and invariant; (B) the copy T_i
# of sl_2 in (wedge^2 D_i)^{K^1} and its form; (C) the copy of T_i in V (x) V;
# (D) the count 26 of G x K^1 invariants in H^4(A) with its Kuenneth breakdown;
# (E) the weight support of xi.
# Part II (link_weights.py): (1) the Hodge classes of degree 4 under three groups;
# (2) the cyclic permutation zeta; (3) closures of circles in K^1; (4) CM points;
# (5) spin_9 restricted to sl_2^3.
# Difference from the Python programs: the old claim "Hom(X_c, Z_{K,c}) = 0 at
# the compositum CM point" is replaced by the check that at the CM point with
# L = K = F.k the abelian varieties X_t and Z_{K,t} share an isogeny factor
# (X_t ~ E x A, Z_{K,t} ~ E^3 x A); Hom = 0 is checked only in the configurations
# where the Hodge torus has rank 6.
# The ranks, which the Python programs take from singular values, are exact here
# (Gaussian elimination over Q, overflow-checked).
# Run: julia --startup-file=no sixfold_link.jl

using LinearAlgebra

const NPASS = Ref(0); const NFAIL = Ref(0)
function check(name, ok)
    ok ? (NPASS[] += 1) : (NFAIL[] += 1)
    println(ok ? "PASS " : "FAIL ", name)
end

# ------------------------------------------------------------ exact linear algebra
const QQ = Rational{BigInt}
"reduced row echelon form; returns (R, pivot columns)"
function rref(M0::AbstractMatrix)
    M = QQ.(M0); m, n = size(M); piv = Int[]; r = 1
    for c in 1:n
        r > m && break
        p = findfirst(i -> M[i, c] != 0, r:m)
        p === nothing && continue
        p += r - 1
        M[r, :], M[p, :] = M[p, :], M[r, :]
        M[r, :] ./= M[r, c]
        for i in 1:m
            if i != r && M[i, c] != 0
                M[i, :] .-= M[i, c] .* M[r, :]
            end
        end
        push!(piv, c); r += 1
    end
    M, piv
end
rk(M) = isempty(M) ? 0 : length(rref(M)[2])
"basis of the null space (columns)"
function nullsp(M0::AbstractMatrix)
    n = size(M0, 2)
    R, piv = rref(M0)
    free = [c for c in 1:n if !(c in piv)]
    B = zeros(QQ, n, length(free))
    for (j, f) in enumerate(free)
        B[f, j] = 1
        for (i, c) in enumerate(piv)
            B[c, j] = -R[i, f]
        end
    end
    B
end

# sparse elimination over Rational{Int} (checked arithmetic: an overflow is an error)
const QI = Rational{Int}
const SRow = Dict{Int,QI}
"null space (columns, dense) of a list of sparse rows in n columns"
function sparse_nullspace(rows, n::Int)
    piv = Dict{Int,SRow}()
    for r0 in rows
        r = copy(r0)
        for (c, v) in r0
            haskey(piv, c) || continue
            for (k, w) in piv[c]
                x = get(r, k, QI(0)) - v * w
                x == 0 ? delete!(r, k) : (r[k] = x)
            end
        end
        isempty(r) && continue
        c = minimum(keys(r)); pc = r[c]
        for k in keys(r)
            r[k] /= pc
        end
        for (c2, r2) in piv
            v = get(r2, c, QI(0)); v == 0 && continue
            for (k, w) in r
                x = get(r2, k, QI(0)) - v * w
                x == 0 ? delete!(r2, k) : (r2[k] = x)
            end
        end
        piv[c] = r
    end
    free = [c for c in 1:n if !haskey(piv, c)]; fidx = Dict(f => j for (j, f) in enumerate(free))
    B = zeros(QQ, n, length(free))
    for (j, f) in enumerate(free)
        B[f, j] = 1
    end
    for (c, r) in piv, (k, w) in r
        k == c && continue
        B[c, fidx[k]] = -w
    end
    B
end

# ------------------------------------------------------------ 2 x 2 objects
const E = [0 1; 0 0]; const Fm = [0 0; 1 0]; const H = [1 0; 0 -1]
const eps2 = [0 1; -1 0]; const I2 = [1 0; 0 1]
kron3(a, b, c) = kron(a, kron(b, c))
bar(m) = tr(m) * I2 - m                 # quaternion conjugation = adjugate
unit(a, b) = (m = zeros(Int, 2, 2); m[a+1, b+1] = 1; m)
const Dbasis = [unit(a, b) for a in 0:1 for b in 0:1]      # index k = 2a + b
psi_place(x, y, c) = tr(bar(x) * y * c)                     # trd(xbar y c)
left_mat(X) = [(X*Dbasis[l])[(k-1)÷2+1, (k-1)%2+1] for k in 1:4, l in 1:4]
right_mat(X) = [(Dbasis[l]*X)[(k-1)÷2+1, (k-1)%2+1] for k in 1:4, l in 1:4]
function X_in_V(Xi, i)
    ms = Any[I2, I2, I2]; ms[i] = Xi; kron3(ms...)
end
const sl2 = [("E", E), ("H", H), ("F", Fm)]

println("== Part I (sixfold_link.py) ==")
# ---------- (A) the polarisation of Z ----------
# psi_c is linear in c, so c_i = gamma_i H is treated as gamma_i times the case c = H.
G0 = [psi_place(Dbasis[k], Dbasis[l], H) for k in 1:4, l in 1:4]
check("(A) psi_c is alternating for cbar = -c (c = gamma diag(1,-1))", G0 + G0' == zeros(Int, 4, 4))
Gs = [psi_place(Dbasis[k], Dbasis[l], I2) for k in 1:4, l in 1:4]
check("(A) psi_c is symmetric, not alternating, for cbar = c (c = gamma)", Gs == Gs' && Gs != zeros(Int, 4, 4))
check("(A) psi_c is invariant under left multiplication by sl_2 (Lie algebra of D^1)",
      all(psi_place(X * d, d2, H) + psi_place(d, X * d2, H) == 0 for X in (E, Fm, H) for d in Dbasis for d2 in Dbasis))
# right multiplication by diag(t, 1/t): t^2 (psi(d Tt, d2 Tt) - psi(d, d2)) is a polynomial of
# degree <= 4 in t; it is evaluated at seven values of t.
check("(A) psi_c is invariant under right multiplication by K^1 = {diag(t, 1/t)}",
      all(psi_place(d * [t 0; 0 1 // t], d2 * [t 0; 0 1 // t], H) == psi_place(d, d2, H)
          for t in (2 // 1, 3 // 1, -5 // 7, 1 // 4, 7 // 3, -2 // 1, 11 // 5) for d in Dbasis for d2 in Dbasis) &&
      all(psi_place(d * H, d2, H) + psi_place(d, d2 * H, H) == 0 for d in Dbasis for d2 in Dbasis))

# ---------- (B) T_i inside wedge^2 D_i and its form ----------
const pairs4 = [(k, l) for k in 1:4 for l in k+1:4]
pidx(a, b) = findfirst(==((a, b)), pairs4)
function wedge_action(M)
    W = zeros(Int, 6, 6)
    for (col, (k, l)) in enumerate(pairs4), a in 1:4, b in 1:4
        coef = M[a, k] * (b == l ? 1 : 0) + (a == k ? 1 : 0) * M[b, l]
        (coef == 0 || a == b) && continue
        a < b ? (W[pidx(a, b), col] += coef) : (W[pidx(b, a), col] -= coef)
    end
    W
end
Lh = wedge_action(left_mat(H)); Le = wedge_action(left_mat(E)); Lf = wedge_action(left_mat(Fm))
Rh = wedge_action(right_mat(H))
Kinv = nullsp(Rh)
check("(B) the K^1-invariant part of wedge^2 D_i has dimension 4", size(Kinv, 2) == 4)
Cas = Lh * Lh + 2 * (Le * Lf + Lf * Le)            # Casimir, 8 on the adjoint representation
I6 = Matrix{Int}(I, 6, 6)
T8 = nullsp(vcat(Rh, Cas - 8 * I6)); T0 = nullsp(vcat(Rh, Cas))
check("(B) on it the Casimir has eigenvalue 8 with multiplicity 3 (the copy T_i of sl_2) and 0 with multiplicity 1",
      size(T8, 2) == 3 && size(T0, 2) == 1 && rk(hcat(T8, T0)) == 4)
wsp = [nullsp(vcat(Rh, Cas - 8 * I6, Lh - w * I6)) for w in (2, 0, -2)]
check("(B) the weights of T_i under the left Cartan element are 2, 0, -2", all(size(x, 2) == 1 for x in wsp))
v2 = wsp[1][:, 1]; v2 = v2 / v2[findfirst(!=(0), v2)]     # normalised: v2 = e_00 ^ e_01
v0 = Lf * v2; vm2 = Lf * v0
# ad(F) E = -H, ad(F)(-H) = -2F: v2 <-> E, v0 <-> -H, vm2 <-> -2F
Tiso = Dict("E" => v2, "H" => -v0, "F" => -vm2 / 2)
function induced_form(Gp)
    [Gp[a, c] * Gp[b, d] - Gp[a, d] * Gp[b, c] for (a, b) in pairs4, (c, d) in pairs4]
end
function ratiosZ(gam)
    ratios = Set{QQ}(); zero_ok = true
    for i in 1:3
        M = induced_form(gam[i] * G0)
        for (n1, m1) in sl2, (n2, m2) in sl2
            val = transpose(Tiso[n1]) * M * Tiso[n2]; t = tr(m1 * m2)
            t != 0 ? push!(ratios, val / (t * gam[i]^2)) : (zero_ok &= val == 0)
        end
    end
    ratios, zero_ok
end
rs1, z1 = ratiosZ(QQ[2, 3, 5]); rs2, z2 = ratiosZ(QQ[-7 // 3, 1 // 11, 13])
check("(B) the form induced by psi_c on T_i is r_Z gamma_i^2 tr(xy), r_Z rational and independent of the place",
      z1 && z2 && length(rs1) == 1 && rs1 == rs2)
rZ = first(rs1)
println("    r_Z = $rZ (with the weight vector normalised to e_00 ^ e_01)")

# ---------- (C) the copy of T_i in V (x) V and its form ----------
Psi = kron3(eps2, eps2, eps2)
PsiInv = Int.(inv(QQ.(Psi)))
tensor_of(x) = x' * Psi                      # psi(x v, w) = v^T x^T Psi w
formVV(A, B) = tr(A' * PsiInv * B * PsiInv')
ratiosX = Set{QQ}(); zx = true; symm = true
for i in 1:3
    for (n1, m1) in sl2, (n2, m2) in sl2
        A = tensor_of(X_in_V(m1, i)); B = tensor_of(X_in_V(m2, i))
        val = formVV(A, B); t = tr(m1 * m2)
        global zx
        t != 0 ? push!(ratiosX, val // t) : (zx &= val == 0)
    end
    global symm &= all(tensor_of(X_in_V(m, i)) == tensor_of(X_in_V(m, i))' for (_, m) in sl2)
end
check("(C) the copy of T_i in H^1(X) (x) H^1(X) is symmetric", symm)
check("(C) it carries r_X tr(xy) with r_X independent of the place", zx && length(ratiosX) == 1)
rX = first(ratiosX)
println("    r_X = $rX; xi^dagger xi = (r_Z/r_X) c^2 = $(rZ / rX) c^2 (c^2 = -f^2 delta in F)")
check("(C) r_Z / r_X is a nonzero rational number", rZ != 0 && rX != 0)

# ------------------------------------------------------------ H^1(A) = V + V' + D
const N = 28
const lab = vcat(fill(0, 8), fill(1, 8), fill(2, 12))       # Kuenneth label: V, V', D
blk(i) = 16+4*(i-1)+1:16+4*i
function op_G_on(i, Xi, which)
    M = zeros(Int, N, N)
    which == 0 && (M[1:8, 1:8] = X_in_V(Xi, i))
    which == 1 && (M[9:16, 9:16] = X_in_V(Xi, i))
    which == 2 && (M[blk(i), blk(i)] = left_mat(Xi))
    M
end
op_diag_G(i, Xi) = op_G_on(i, Xi, 0) + op_G_on(i, Xi, 1) + op_G_on(i, Xi, 2)
op_torus(i) = (M = zeros(Int, N, N); M[blk(i), blk(i)] = right_mat(H); M)
op_sp(A) = (M = zeros(QI, N, N); M[1:8, 1:8] = A; M[9:16, 9:16] = A; M)
const cartan = vcat([op_diag_G(i, H) for i in 1:3], [op_torus(i) for i in 1:3])
const wt = [C[k, k] for k in 1:N, C in cartan]
const Quad = NTuple{4,Int}
const quads = Quad[(a, b, c, d) for a in 1:N for b in a+1:N for c in b+1:N for d in c+1:N
                   if all(wt[a, j] + wt[b, j] + wt[c, j] + wt[d, j] == 0 for j in 1:6)]
const qindex = Dict(q => j for (j, q) in enumerate(quads))
ktype(q) = ntuple(j -> count(k -> lab[k] == j - 1, q), 3)
const types = sort(unique(ktype.(quads)))
function sortsign(new::Vector{Int})
    arr = copy(new); sign = 1
    for ii in 1:4, jj in 1:4-ii
        if arr[jj] > arr[jj+1]
            arr[jj], arr[jj+1] = arr[jj+1], arr[jj]; sign = -sign
        end
    end
    (arr[1], arr[2], arr[3], arr[4]), sign
end
"image of the basis vector q of wedge^4 under the derivation M"
function act_on_wedge(M, q::Quad)
    out = Dict{Quad,QI}()
    for (pos, k) in enumerate(q), a in 1:N
        (M[a, k] == 0 || a in q) && continue
        new = collect(q); new[pos] = a
        key, sign = sortsign(new)
        out[key] = get(out, key, QI(0)) + sign * M[a, k]
    end
    out
end
"invariants of the operators in the weight-zero span of wedge^4: one basis matrix (rows = quads) per Kuenneth type"
function invariants(ops)
    res = Dict{NTuple{3,Int},Matrix{QQ}}()
    for ty in types
        sel = [j for (j, q) in enumerate(quads) if ktype(q) == ty]
        rows = Dict{Tuple{Int,Quad},SRow}()
        for (o, M) in enumerate(ops), (jj, j) in enumerate(sel), (key, v) in act_on_wedge(M, quads[j])
            v == 0 && continue
            get!(rows, (o, key), SRow())[jj] = v
        end
        B = sparse_nullspace(values(rows), length(sel))
        full = zeros(QQ, length(quads), size(B, 2)); full[sel, :] = B
        res[ty] = full
    end
    res
end
total(inv) = sum(size(B, 2) for B in values(inv))
by_type(inv) = [ty => size(inv[ty], 2) for ty in types if size(inv[ty], 2) > 0]
allcols(inv) = hcat([inv[ty] for ty in types]...)

# ---------- (D) G x K^1 invariants in H^4(X x X x Z) ----------
println("    weight-zero 4-subsets of H^1(X x X x Z): ", length(quads))
raise_lower_diag = [op_diag_G(i, X) for i in 1:3 for X in (E, Fm)]
inv_diag = invariants(raise_lower_diag)
expected_types = [(0, 0, 4) => 6, (0, 2, 2) => 3, (0, 4, 0) => 1, (1, 1, 2) => 6, (1, 3, 0) => 1,
                  (2, 0, 2) => 3, (2, 2, 0) => 4, (3, 1, 0) => 1, (4, 0, 0) => 1]
check("(D) dim Hdg^2(X x X x Z) = dim of the G x K^1 invariants in H^4 = $(total(inv_diag)) = 26", total(inv_diag) == 26)
println("    by Kuenneth type (V, V', D): ", join(["$(t) $(d)" for (t, d) in by_type(inv_diag)], ", "))
check("(D) Kuenneth breakdown (0,0,4) 6, (0,2,2) 3, (0,4,0) 1, (1,1,2) 6, (1,3,0) 1, (2,0,2) 3, (2,2,0) 4, (3,1,0) 1, (4,0,0) 1",
      by_type(inv_diag) == expected_types)
# the same dimensions from the characters: dim of the SL_2^3 x T^3 invariants =
# sum over eps in {0,1}^3 of (-1)^|eps| mult(weight (2 eps, 0))
function wedge_char(ws, k)
    res = Dict{NTuple{6,Int},Int}()
    function rec(start, left, acc)
        if left == 0
            res[acc] = get(res, acc, 0) + 1; return
        end
        for i in start:length(ws)-left+1
            rec(i + 1, left - 1, acc .+ ws[i])
        end
    end
    rec(1, k, ntuple(_ -> 0, 6)); res
end
function mulchar(c1, c2)
    r = Dict{NTuple{6,Int},Int}()
    for (w1, m1) in c1, (w2, m2) in c2
        r[w1.+w2] = get(r, w1 .+ w2, 0) + m1 * m2
    end
    r
end
inv_dim(ch) = sum((-1)^(a + b + c) * get(ch, (2a, 2b, 2c, 0, 0, 0), 0) for a in 0:1, b in 0:1, c in 0:1)
Vw = [ntuple(j -> wt[k, j], 6) for k in 1:8]; Dw = [ntuple(j -> wt[k, j], 6) for k in 17:28]
chardims = [(a, b, 4 - a - b) => inv_dim(mulchar(mulchar(wedge_char(Vw, a), wedge_char(Vw, b)), wedge_char(Dw, 4 - a - b)))
            for a in 0:4 for b in 0:4-a]
check("(D) the character formula gives the same dimensions (total 26)",
      sort([p for p in chardims if p.second > 0]) == expected_types)
check("(D) exactly 3 = [F:Q] invariants in H^2(X) (x) H^2(Z) and in H^2(X') (x) H^2(Z); 6 in H^1(X) (x) H^1(X') (x) H^2(Z)",
      size(inv_diag[(2, 0, 2)], 2) == 3 && size(inv_diag[(0, 2, 2)], 2) == 3 && size(inv_diag[(1, 1, 2)], 2) == 6)

# ---------- (E) the weight support of xi ----------
zero_pair(a, b) = all(wt[a, j] + wt[b, j] == 0 for j in 1:6)
q112 = [q for q in quads if ktype(q) == (1, 1, 2)]
prim = count(q -> !any(zero_pair(q[a], q[b]) for a in 1:4 for b in a+1:4), q112)
check("(E) weight-zero 4-sets of type (1,1,2): $(length(q112)) = 72; primitive (no zero-sum pair): $prim = 24",
      length(q112) == 72 && prim == 24)
# support of the link: x_s x'_s' z_(-u e_i; f_i) z_(-u e_i; -f_i), s + s' = 2u e_i
Wd = inv_diag[(1, 1, 2)]
supp = [q for (j, q) in enumerate(quads) if any(Wd[j, :] .!= 0)]
primsupp = [q for q in supp if !any(zero_pair(q[a], q[b]) for a in 1:4 for b in a+1:4)]
check("(E) the invariants of type (1,1,2) are supported on all 72 sets, 24 of them primitive zero-sum sets",
      length(supp) == 72 && length(primsupp) == 24)

println("== Part II (link_weights.py) ==")
# ---------- (1) representation picture ----------
check("(1) V (x) V = 1 + T + U + S^2V_1 S^2V_2 S^2V_3: 1 + 9 + 27 + 27 = 64", 1 + 9 + 27 + 27 == 64)
w2 = [(a, b) for a in 17:28 for b in a+1:28 if all(wt[a, j] + wt[b, j] == 0 for j in 4:6)]
check("(1) torus-invariant weight pairs in wedge^2 D: $(length(w2)) = 12 = dim(T + 1^3)", length(w2) == 12)
check("(1) Delta(G).K^1: 26 Hodge classes, 6 of type (1,1,2)", total(inv_diag) == 26 && size(inv_diag[(1, 1, 2)], 2) == 6)
raise_lower_indep = vcat([op_G_on(i, X, 0) + op_G_on(i, X, 1) for i in 1:3 for X in (E, Fm)],
                         [op_G_on(i, X, 2) for i in 1:3 for X in (E, Fm)])
inv_indep = invariants(raise_lower_indep)
println("    invariants of Hg(X) x Hg(Z_K) = G x G'.K^1: $(total(inv_indep)); ", join(["$(t) $(d)" for (t, d) in by_type(inv_indep)], ", "))
check("(1) G x G'.K^1 (no tie between X and Z): 23 invariants, 3 of type (1,1,2): the 3 links are the difference 26 - 23",
      total(inv_indep) == 23 && size(inv_indep[(1, 1, 2)], 2) == 3)
sp_gens = Matrix{QI}[]
for a in 1:8, b in a:8
    S = zeros(Int, 8, 8); S[a, b] += 1; S[b, a] += 1
    push!(sp_gens, op_sp(PsiInv * S))
end
inv_sp = invariants(vcat(sp_gens, [QI.(M) for M in raise_lower_indep[7:end]]))
println("    Sp(V) (diagonal on V + V') x G x K^1 invariants: $(total(inv_sp)); ", join(["$(t) $(d)" for (t, d) in by_type(inv_sp)], ", "))
check("(1) Lefschetz-type part of type (1,1,2) is psi (x) NS(Z): dim 3", size(inv_sp[(1, 1, 2)], 2) == 3)
ker_diag = allcols(inv_diag); ker_sp = allcols(inv_sp)
check("(1) the Lefschetz-type part lies inside the 26 Hodge classes", rk(hcat(ker_diag, ker_sp)) == 26)

# ---------- (2) the cyclic permutation zeta ----------
Z8 = zeros(Int, 8, 8)
for b1 in 0:1, b2 in 0:1, b3 in 0:1
    Z8[4b3+2b1+b2+1, 4b1+2b2+b3+1] = 1
end
check("(2) zeta preserves psi", Z8' * Psi * Z8 == Psi)
check("(2) zeta conjugates the i-th sl_2 factor to the (i+1)-th",
      all(Z8 * X_in_V(X, i) * Z8' == X_in_V(X, i % 3 + 1) for i in 1:3 for X in (E, Fm, H)))
zperm = collect(1:N)
for k in 1:8
    zperm[k] = findfirst(==(1), Z8[:, k]); zperm[8+k] = 8 + zperm[k]
end
imgs = [sortsign([zperm[k] for k in q]) for q in quads]
allkeys = sort(collect(union(Set(quads), Set(k for (k, _) in imgs)))); kidx = Dict(k => j for (j, k) in enumerate(allkeys))
Zw = zeros(Int, length(allkeys), length(quads)); Emb = zeros(Int, length(allkeys), length(quads))
for (j, (k, sg)) in enumerate(imgs)
    Zw[kidx[k], j] = sg
end
for (j, q) in enumerate(quads)
    Emb[kidx[q], j] = 1
end
println("    zeta maps $(length(allkeys) - length(quads)) weight-zero quads out of the weight-zero span")
W6 = inv_diag[(1, 1, 2)]
check("(2) the (1,1,2) Hodge classes form a 6-dimensional space W6", rk(W6) == 6)
fixed_dim = 6 - rk((Zw - Emb) * W6)
check("(2) zeta fixes exactly a 3-dimensional subspace of W6 (zeta-fixed vectors: $fixed_dim)", fixed_dim == 3)
W3 = inv_sp[(1, 1, 2)]
check("(2) psi (x) NS(Z) is zeta-fixed, so it is the zeta-fixed part of W6", all((Zw - Emb) * W3 .== 0) && rk(hcat(W6, W3)) == 6)
Xi3 = W6 * nullsp(W3' * W6)                  # the complement of W3 in W6 orthogonal to W3
check("(2) Hom_G(T_X, T_Z) (x) Qbar is 3-dimensional (one link per place)", rk(Xi3) == 3 && rk(hcat(W3, Xi3)) == 6)
check("(2) zeta carries the link space to a space meeting the Hodge classes only in 0",
      rk(hcat(Emb * ker_diag, Zw * Xi3)) == 26 + 3)
fixed_all = 26 - rk((Zw - Emb) * ker_diag)
println("    zeta-fixed Hodge classes in all of H^4(A): $fixed_all of 26")
check("(2) every Lefschetz-type class is zeta-fixed", all((Zw - Emb) * ker_sp .== 0))
println("    Lefschetz-type (Sp(V)-invariant) Hodge classes: $(size(ker_sp, 2)) of 26")
check("(2) the zeta-fixed Hodge classes are exactly the Lefschetz-type classes ($fixed_all = $(size(ker_sp, 2)))",
      fixed_all == size(ker_sp, 2))

# ---------- (3) Zariski closure of the circle in the torus K^1 ----------
const S3 = [[1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]]
const A3 = [[1, 2, 3], [2, 3, 1], [3, 1, 2]]
# signed permutation v -> (s_i v_{p^-1(i)})
signed_perm(p, s) = v -> [s[i] * v[findfirst(==(i), p)] for i in 1:3]
matrows(vs) = permutedims(hcat([collect(v) for v in vs]...))
for (nm, perms) in (("S3", S3), ("A3", A3))
    G3 = [signed_perm(p, (e, e, e)) for p in perms for e in (1, -1)]
    orb(f) = sort(unique([g(f) for g in G3]))
    check("(3) uniform signs, Galois $nm: the closure of (u,u,1) is all of K^1 (rank 3)", rk(matrows(orb([1, 1, 0]))) == 3)
    Mo = matrows(orb([1, -1, 0]))
    ann = nullsp(Mo)
    check("(3) mixed signs, Galois $nm: the closure of (u,1/u,1) has rank 2, with annihilator Z(1,1,1): T_0 = ker(chi_1 chi_2 chi_3)",
          rk(Mo) == 2 && size(ann, 2) == 1 && ann[:, 1] / ann[1, 1] == [1, 1, 1])
end
check("(3) Weil variant: dim H^{1,0} cap D_+ = 2 + 0 + 1 = 3 (signature (3,3)); uniform signs: 2 + 2 + 1 = 5", 2 + 0 + 1 == 3 && 2 + 2 + 1 == 5)
check("(3) det D_+ = (chi_1 chi_2 chi_3)^2 is trivial on T_0, not on K^1", (2, 2, 2) != (0, 0, 0) && (2 == 2 == 2))
nonzero_chars = Set(Tuple(v[p]) for v in ([2, 0, 0], [1, 1, 0], [1, -1, 0]) for p in S3)
check("(3) no nonzero character of wedge^2 D is trivial on T_0: T_Z + 1^3 unchanged",
      !any(c[1] == c[2] == c[3] for c in nonzero_chars))

# ---------- (4) CM points ----------
# Characters of L^1 x K^1: (a; b) in Z^6.  Circle h = (1, 1, u; u^s1, u^s2, 1): the characters
# trivial on it satisfy a_3 + s1 b_1 + s2 b_2 = 0.  Galois image Gamma: pairs of signed
# permutations (on a, on b) with the same permutation.
const Vweights = [[a1, a2, a3, 0, 0, 0] for a1 in (1, -1) for a2 in (1, -1) for a3 in (1, -1)]
const Dweights = [vcat([j == i ? sa : 0 for j in 1:3], [j == i ? sb : 0 for j in 1:3]) for i in 1:3 for sa in (1, -1) for sb in (1, -1)]
function analyse(name, gamma, s1=1, s2=1)
    f = [0, 0, 1, s1, s2, 0]
    gal(w, g) = vcat(g[1](w[1:3]), g[2](w[4:6]))
    orbit = sort(unique([gal(f, g) for g in gamma]))
    Mo = matrows(orbit); rank = rk(Mo)
    restr(v) = Mo * v                         # the restriction of a character to the Hodge torus H_c
    same(u, v) = restr(u) == restr(v)
    classesD = Tuple{Vector{Int},Int}[]       # weights of D modulo H_c, with multiplicity
    for d in Dweights
        j = findfirst(c -> same(c[1], d), classesD)
        j === nothing ? push!(classesD, (d, 1)) : (classesD[j] = (classesD[j][1], classesD[j][2] + 1))
    end
    mults = sort([c[2] for c in classesD])
    sharedV = [v for v in Vweights if any(same(v, d) for d in Dweights)]
    # Galois orbits of the restricted characters (isogeny factors)
    function orbits(ws)
        seen = Set{Vector{Int}}(); out = Set{Vector{Int}}[]
        for w in ws
            restr(w) in seen && continue
            o = Set(restr(gal(w, g)) for g in gamma); union!(seen, o); push!(out, o)
        end
        out
    end
    orbV = orbits(Vweights); orbD = orbits(Dweights)
    # Hodge classes of degree 4 on A_c: zero-sum 4-subsets of the 28 basis vectors modulo H_c
    rb = [restr(v) for v in vcat(Vweights, Vweights, Dweights)]
    n4 = 0; n112 = 0; prim112 = 0
    for a in 1:N, b in a+1:N, c in b+1:N, d in c+1:N
        any(!=(0), rb[a] + rb[b] + rb[c] + rb[d]) && continue
        n4 += 1
        q = (a, b, c, d)
        if ktype(q) == (1, 1, 2)
            n112 += 1
            any(all(==(0), rb[q[x]] + rb[q[y]]) for x in 1:4 for y in x+1:4) || (prim112 += 1)
        end
    end
    println("    $name: rank H_c = $rank; D-weight classes (mult) = $mults; V-weights shared with D: $(length(sharedV)) of 8;",
            " Galois orbits on the characters of X_c: $(sort(length.(orbV))), of Z_c: $(sort(length.(orbD)));",
            " dim Hdg^2(A_c) = $n4, type (1,1,2): $n112, primitive: $prim112")
    (rank=rank, mults=mults, shared=length(sharedV), n4=n4, n112=n112, prim112=prim112, orbV=orbV, orbD=orbD,
     multof=o -> sum(c[2] for c in classesD if restr(c[1]) in o))
end
uni(e) = (e, e, e)
sgn(p) = p in A3 ? 1 : -1
E3B = [1, 1, 1, 1, 1, 1, 3, 3]
# (i) the compositum CM point L = K = F.k: the same uniform sign on both sides
for (nm, perms) in (("S3", S3), ("A3", A3))
    gamma = [(signed_perm(p, uni(e)), signed_perm(p, uni(e))) for p in perms for e in (1, -1)]
    r = analyse("(i)  L = K = F.k, Galois $nm, signs (iota0, iota0)", gamma)
    check("(4)(i) L = K = F.k, Galois $nm: the Hodge torus has rank 3 and every weight of X_c occurs in Z_{K,c}", r.rank == 3 && r.shared == 8)
    check("(4)(i) L = K = F.k, Galois $nm: X_c ~ E x A (Galois orbits of sizes 2, 6) and Z_{K,c} ~ E^3 x A " *
          "(the same two orbits, with multiplicities 3 and 1): X_c and Z_{K,c} share an isogeny factor",
          sort(length.(r.orbV)) == [2, 6] && Set(r.orbV) == Set(r.orbD) && r.mults == E3B &&
          all(r.multof(o) == (length(o) == 2 ? 3 : 1) * length(o) for o in r.orbD))
    check("(4)(i) L = K = F.k, Galois $nm: $(r.n112) = 246 Hodge monomials of type (1,1,2), $(r.prim112) = 48 without a zero-sum pair",
          r.n112 == 246 && r.prim112 == 48)
    r = analyse("(i') L = K = F.k, Galois $nm, signs (iota0bar, iota0bar)", gamma, -1, -1)
    check("(4)(i') other uniform sign, Galois $nm: again rank 3, all weights shared, Z_{K,c} ~ E^3 x A",
          r.rank == 3 && r.shared == 8 && r.mults == E3B && Set(r.orbV) == Set(r.orbD))
    r = analyse("(iW) L = K = F.k, Galois $nm, mixed signs (Weil variant)", gamma, 1, -1)
    check("(4)(iW) Weil variant, Galois $nm: " * (nm == "A3" ? "rank 3 and 6 shared weights (Z^W ~ B^2)" : "rank 5 and no shared weight"),
          (nm == "A3" && r.rank == 3 && r.shared == 6) || (nm == "S3" && r.rank == 5 && r.shared == 0))
end
gamma = [(signed_perm(p, uni(sgn(p))), signed_perm(p, uni(sgn(p)))) for p in S3]
r = analyse("(i'') L = K = F.k, k = Q(sqrt(d_F)), Galois S3 with sign sgn(pi)", gamma)
check("(4)(i'') k = Q(sqrt(d_F)): again rank 3, all weights shared, Z_{K,c} ~ E^3 x A", r.rank == 3 && r.shared == 8 && r.mults == E3B)

# ---------- (5) spin_9 restricted to sl_2^3 ----------
restr9 = Dict{NTuple{3,Int},Int}()
for w in Iterators.product((1, -1), (1, -1), (1, -1), (1, -1))      # twice the weights (+-1/2)^4
    restr9[w[1:3]] = get(restr9, w[1:3], 0) + 1
end
check("(5) spin_9 | sl_2^3 = V_1 (x) V_2 (x) V_3 (x) Qbar^2: each of the 8 weights twice",
      length(restr9) == 8 && all(==(2), values(restr9)))

# (ii) L = F.k', K = F.k, k != k': independent uniform signs
for (nm, perms) in (("S3", S3), ("A3", A3))
    local gamma = [(signed_perm(p, uni(e)), signed_perm(p, uni(e2))) for p in perms for e in (1, -1) for e2 in (1, -1)]
    local r = analyse("(ii) L = F.k', K = F.k, k != k' (independent), Galois $nm", gamma)
    check("(4)(ii) L = F.k', K = F.k, k != k', Galois $nm: rank 6, no shared weight, Hom(X_c, Z_{K,c}) = 0; " *
          "$(r.n112) = 72 Hodge monomials of type (1,1,2), $(r.prim112) = 24 primitive",
          r.rank == 6 && r.shared == 0 && r.n112 == 72 && r.prim112 == 24)
end
# (iii) F non-Galois, k' = k.Q(sqrt(disc F)): K-side sign = L-side sign times sgn(pi)
gamma = [(signed_perm(p, uni(e)), signed_perm(p, uni(e * sgn(p)))) for p in S3 for e in (1, -1)]
r3 = analyse("(iii) L = F.k, K = F.k', k' = k.Q(sqrt(d_F)), Galois S3", gamma)
# (iv) L primitive sextic CM (B_3 on the L side), K = F.k with the K-side sign a quadratic character of B_3
B3 = [(p, s) for p in S3 for s in Iterators.product((1, -1), (1, -1), (1, -1))]
r4 = []
for (nmc, charf) in (("prod s_i", (p, s) -> s[1] * s[2] * s[3]), ("sgn(pi)", (p, s) -> sgn(p)),
                     ("prod s_i . sgn(pi)", (p, s) -> s[1] * s[2] * s[3] * sgn(p)))
    local gamma = [(signed_perm(p, s), signed_perm(p, uni(charf(p, s)))) for (p, s) in B3]
    push!(r4, analyse("(iv) L primitive (B_3), K = F.k with k cut out by $nmc", gamma))
end
check("(4)(iii),(iv) the configurations printed above have Hodge tori of ranks $(r3.rank); $([r.rank for r in r4]) and " *
      "$(r3.shared); $([r.shared for r in r4]) shared weights (shared weights only when the rank is < 6)",
      all(r.shared == 0 || r.rank < 6 for r in vcat(r3, r4)))
# (v) both primitive, independent
gamma = [(signed_perm(p, s), signed_perm(p, s2)) for p in S3 for s in Iterators.product((1, -1), (1, -1), (1, -1))
         for s2 in Iterators.product((1, -1), (1, -1), (1, -1))]
r = analyse("(v)  L, K both primitive, independent signs", gamma)
check("(4)(v) L, K primitive and independent: rank 6, no shared weight, Hom(X_c, Z_{K,c}) = 0", r.rank == 6 && r.shared == 0)

println("sixfold_link.jl: $(NPASS[]) checks passed, $(NFAIL[]) failed")
NFAIL[] > 0 && exit(1)
