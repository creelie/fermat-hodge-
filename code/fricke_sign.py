"""
Certificate for the sign lemma of the Fricke families (Lemma V.8 and Theorem
V.9 of the paper): the Fricke self-isogeny of the twisted families composes
to [-N], so the families have complex multiplication by Q(sqrt(-N)), and the
sign changes only at the twists by the fixed points of the Fricke involution.

For N in {5, 7} let E_t: y^2 = x^3 + A(t) x + B(t), A = -27 c_4, B = -54 c_6,
be the Fricke universal curve over X_0(N) with the Fricke involution
w(t) = N^k / t (k = 3 for N = 5, k = 2 for N = 7), and let C_t be the cyclic
subgroup of order N of the generic fibre that is rational over C(t).  The
program computes exactly, in sympy over Q(t):

  (A) the division polynomial psi_N of E_t and its factor of degree (N-1)/2
      in x, the kernel polynomial of C_t (its roots are the x-coordinates of
      the nonzero points of C_t);
  (B) Velu's isogeny E_t -> E'_t with kernel C_t, which pulls the invariant
      differential of E' back to that of E_t, and the j-invariant check
      j(E') = j(E_{w(t)}): E' is E_{w(t)} up to the isomorphism
      (x, y) -> (lambda^-2 x, lambda^-3 y);
  (C) lambda(t)^2, where the composite isogeny phi: E_t -> E_{w(t)} pulls
      dx/y back to lambda(t) dx/y: lambda^2 = -t^2 / 25 for N = 5 and
      -t^2 / 7 for N = 7, and lambda(t) lambda(w(t)) = -N, so the composite
      E_t -> E_{w(t)} -> E_t is [-N] on the generic fibre;
  (D) the twist bookkeeping: for the twist by u(t) = (t - p)(t - N^k / p)
      one has u(w(t)) = (N^k / t^2) u(t), the isomorphism of twists scales
      dx/y by c(t) = t / N^{k/2}, and the two-form dt dx/y of the surface is
      multiplied by Lambda = w'(t) c(t) lambda(t) with Lambda^2 = -N; for
      the twist by t^2 - N^k, fixed by w, u(w(t)) = -(N^k / t^2) u(t) and
      Lambda^2 = +N (the surfaces of van Geemen and Schuett with real
      multiplication);
  (E) the polynomial identity N B'(t) A~(t) + A'(t) B~(t) = 0 behind (C),
      with A~(t) = t^4 A(N^k / t) and B~(t) = t^6 B(N^k / t), which the Lean
      file proves from the same kernel polynomials (theorems fricke_sign_5,
      fricke_sign_7);
  (F) the analytic model: f_tau(z) = z / tau maps C / (Z tau + Z) onto
      C / (Z w(tau) + Z) with kernel <1/N>, w(tau) = -1 / (N tau), and
      f_{w(tau)} o f_tau = [-N].
Run:  python3 -I fricke_sign.py
"""
import sympy as sp

checks = []
def check(name, ok):
    checks.append(bool(ok))
    print(("PASS  " if ok else "FAIL  ") + name)

t, x, tau = sp.symbols('t x tau')
DATA = {
    7: dict(c4=(t**2+13*t+49)*(t**2+5*t+1),
            c6=(t**2+13*t+49)*(t**4+14*t**3+63*t**2+70*t-7), Nk=49),
    5: dict(c4=(t**2+10*t+5)*(t**2+22*t+125),
            c6=(t**2+4*t-1)*(t**2+22*t+125)**2, Nk=125),
}

def division_polynomials(A, B, N):
    """f_n with psi_n = f_n (n odd) and psi_n = 2y f_n (n even) for y^2 = x^3 + A x + B."""
    y2 = x**3 + A*x + B
    f = {0: sp.Integer(0), 1: sp.Integer(1), 2: sp.Integer(1),
         3: 3*x**4 + 6*A*x**2 + 12*B*x - A**2,
         4: 2*(x**6 + 5*A*x**4 + 20*B*x**3 - 5*A**2*x**2 - 4*A*B*x - 8*B**2 - A**3)}
    def F(n):
        if n in f:
            return f[n]
        m = n // 2
        if n % 2 == 1:
            if m % 2 == 0:
                r = F(m+2)*F(m)**3*(4*y2)**2 - F(m-1)*F(m+1)**3
            else:
                r = F(m+2)*F(m)**3 - F(m-1)*F(m+1)**3*(4*y2)**2
        else:
            r = F(m)*(F(m+2)*F(m-1)**2 - F(m-2)*F(m+1)**2)
        f[n] = sp.expand(r)
        return f[n]
    return F(N)

def jinv(a, b):
    return sp.factor(sp.together(1728*4*a**3/(4*a**3 + 27*b**2)))

KERNELS = {}
for N in (5, 7):
    d = DATA[N]; Nk = d['Nk']
    A = sp.expand(-27*d['c4']); B = sp.expand(-54*d['c6'])
    m = (N - 1)//2
    psiN = division_polynomials(A, B, N)
    check(f"N={N}: psi_N has degree (N^2-1)/2 = {(N*N-1)//2} in x",
          sp.Poly(psiN, x).degree() == (N*N - 1)//2)
    kers = [sp.Poly(fac, x).monic() for fac, e in sp.factor_list(psiN, x, t)[1]
            if sp.Poly(fac, x).degree() == m]
    check(f"N={N}: psi_N has exactly one irreducible factor of degree (N-1)/2 in x, the kernel polynomial, and it divides psi_N",
          len(kers) == 1 and sp.Poly(psiN, x).rem(sp.Poly(kers[0].as_expr(), x)).is_zero)
    ker = kers[0]
    KERNELS[N] = ker
    print("      kernel polynomial:", sp.expand(ker.as_expr()))
    coeffs = ker.all_coeffs()                        # x^m + k_1 x^{m-1} + ... + k_m
    e = [sp.Integer(1)] + [sp.expand((-1)**(i+1)*coeffs[i+1]) for i in range(m)]
    # Newton: power sums S_1, S_2, S_3 of the roots
    S = [sp.Integer(m)]
    for r in range(1, 4):
        s = sum((-1)**(i-1)*e[i]*S[r-i] for i in range(1, min(r-1, m)+1))
        if r <= m:
            s += (-1)**(r-1)*r*e[r]
        S.append(sp.expand(s))
    S1, S2, S3 = S[1], S[2], S[3]
    tt = sp.expand(6*S2 + 2*A*m)                    # Velu: sum of t_Q over the kernel
    ww = sp.expand(10*S3 + 6*A*S1 + 4*B*m)          # Velu: sum of u_Q + x_Q t_Q
    A2 = sp.expand(A - 5*tt); B2 = sp.expand(B - 7*ww)
    Aw = sp.together(A.subs(t, sp.Rational(Nk)/t)); Bw = sp.together(B.subs(t, sp.Rational(Nk)/t))
    check(f"N={N}: Velu's curve has j(E') = j(E_w(t))", sp.simplify(jinv(A2, B2) - jinv(Aw, Bw)) == 0)
    check(f"N={N}: j(E') is not j(E_t) (the isogeny is not an endomorphism)",
          sp.simplify(jinv(A2, B2) - jinv(A, B)) != 0)
    # E' = E_w up to (x,y) -> (u^2 x, u^3 y) with u^4 = A'/A(w), u^6 = B'/B(w); lambda = u^{-1}
    lam2 = sp.factor(sp.together(B2*Aw/(A2*Bw)))     # lambda^2 = u^{-2}, u^2 = A2 Bw / (B2 Aw)
    expected = {5: -t**2/sp.Integer(25), 7: -t**2/sp.Integer(7)}[N]
    check(f"N={N}: lambda(t)^2 = {expected}", sp.simplify(lam2 - expected) == 0)
    check(f"N={N}: lambda^4 = A'/A(w) and lambda^6 = B'/B(w) are consistent",
          sp.simplify(lam2**2 - A2/Aw) == 0 and sp.simplify(lam2**3 - B2/Bw) == 0)
    lam2w = sp.together(lam2.subs(t, sp.Rational(Nk)/t))
    check(f"N={N}: lambda(t)^2 lambda(w(t))^2 = N^2", sp.simplify(lam2*lam2w - N*N) == 0)
    # the product lambda(t) lambda(w(t)) with lambda = c*t*i (constant c): c^2 t^2 (-1) * (Nk/t)^2 ... = -N
    c = sp.sqrt(-expected/t**2)                      # lambda = i c t up to sign, c^2 = 1/25 or 1/7
    prod = sp.simplify(sp.I*c*t * sp.I*c*(sp.Rational(Nk)/t))
    check(f"N={N}: lambda(t) lambda(w(t)) = -N exactly (both signs of lambda give the same product)",
          prod == -N)
    # (D) twists
    p = sp.symbols('p')
    u = (t - p)*(t - sp.Rational(Nk)/p)
    check(f"N={N}: u_p(w(t)) = (N^k / t^2) u_p(t) for the pair twist",
          sp.simplify(u.subs(t, sp.Rational(Nk)/t) - sp.Rational(Nk)/t**2*u) == 0)
    ufix = t**2 - Nk
    check(f"N={N}: u(w(t)) = -(N^k / t^2) u(t) for the fixed-point twist t^2 - N^k",
          sp.simplify(ufix.subs(t, sp.Rational(Nk)/t) + sp.Rational(Nk)/t**2*ufix) == 0)
    wprime = sp.diff(sp.Rational(Nk)/t, t)
    Lam2_pair = sp.simplify(wprime**2 * (t**2/sp.Rational(Nk)) * lam2)
    Lam2_fix = sp.simplify(wprime**2 * (-t**2/sp.Rational(Nk)) * lam2)
    check(f"N={N}: Lambda^2 = w'(t)^2 c(t)^2 lambda(t)^2 = -N on the pair twists", Lam2_pair == -N)
    check(f"N={N}: Lambda^2 = +N on the fixed-point twist", Lam2_fix == N)
    # (E) polynomial identity for Lean: N B' A~ + A' B~ = 0
    At = sp.expand(t**4*A.subs(t, sp.Rational(Nk)/t)); Bt = sp.expand(t**6*B.subs(t, sp.Rational(Nk)/t))
    check(f"N={N}: A~ = t^4 A(N^k/t) and B~ = t^6 B(N^k/t) are polynomials",
          sp.together(At).as_numer_denom()[1] == 1 and sp.together(Bt).as_numer_denom()[1] == 1)
    ident = sp.expand({5: 25, 7: 7}[N]*B2*At + A2*Bt)
    check(f"N={N}: {25 if N == 5 else 7} B'(t) A~(t) + A'(t) B~(t) = 0 as polynomials", ident == 0)
    # print the data used by the Lean theorems
    def coeff_list(poly):
        P = sp.Poly(sp.expand(poly), t)
        return [int(P.coeff_monomial(t**i)) for i in range(P.degree() + 1)]
    print("      Lean data: A =", coeff_list(A))
    print("      Lean data: B =", coeff_list(B))
    print("      Lean data: kernel k_i =", [coeff_list(c) for c in coeffs[1:]])
    print("      Lean data: A' =", coeff_list(A2), " B' =", coeff_list(B2))
    print("      Lean data: A~ =", coeff_list(At), " B~ =", coeff_list(Bt))

# (F) the analytic model
f = lambda z, ta: z/ta
w_tau = -1/(N*tau)
for N in (5, 7):
    z = sp.symbols('z')
    composite = sp.simplify(f(f(z, tau), -1/(N*tau)))
    check(f"N={N}: f_w(tau) o f_tau (z) = z / (tau w(tau)) = -N z", sp.simplify(composite + N*z) == 0)
    # kernel of z -> z/tau on C/(Z tau + Z): z/tau in Z + Z w(tau) iff z in Z tau + (1/N) Z
    a, b = sp.symbols('a b', integer=True)
    zker = sp.expand(tau*(a + b*(-1/(N*tau))))
    check(f"N={N}: the kernel of f_tau is generated by 1/N modulo Z tau + Z", sp.simplify(zker - (a*tau - b/sp.Integer(N))) == 0)

fails = sum(1 for c in checks if not c)
print(f"fricke_sign: {len(checks) - fails} checks passed, {fails} failed")
