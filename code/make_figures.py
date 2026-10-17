"""Figures of the paper: 3D plots drawn with matplotlib.

Run from the repository root:  python3 code/make_figures.py
Writes PDF (vector) and PNG (200 dpi) files to paper/figures/.
"""
import os
import numpy as np
import matplotlib
import matplotlib.colors
import matplotlib.patches
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D  # noqa: F401
from mpl_toolkits.mplot3d.art3d import Poly3DCollection

OUT = os.path.join(os.path.dirname(__file__), "..", "paper", "figures")
os.makedirs(OUT, exist_ok=True)
plt.rcParams.update({"font.family": "serif", "font.size": 10,
                     "mathtext.fontset": "cm"})


def save(fig, name):
    fig.savefig(os.path.join(OUT, name + ".pdf"), bbox_inches="tight")
    fig.savefig(os.path.join(OUT, name + ".png"), dpi=200, bbox_inches="tight")
    plt.close(fig)


def fig_locus():
    """The period domain of a Weil family as a surface; the algebraic locus
    is a dense countable union of closed strata (curves and points), and the
    dichotomy says it is either everything or meagre."""
    fig = plt.figure(figsize=(7.0, 3.6))
    ax = fig.add_subplot(111, projection="3d")
    u = np.linspace(-1.6, 1.6, 60)
    v = np.linspace(-1.6, 1.6, 60)
    U, V = np.meshgrid(u, v)
    Z = 0.25 * (U**2 - V**2)
    ax.plot_surface(U, V, Z, color="#dfe7f2", alpha=0.85, linewidth=0,
                    antialiased=True)
    rng = np.random.default_rng(3)
    # dense strata: Hecke translates of the CM base point and of special curves
    for k in range(14):
        t = np.linspace(-1.5, 1.5, 80)
        a, b = rng.uniform(-1.2, 1.2), rng.uniform(-1, 1)
        x = a + 0.35 * np.cos(2.2 * t + b) * t
        y = t
        ax.plot(x, y, 0.25 * (x**2 - y**2) + 0.01, color="#7a1f1f", lw=0.8)
    pts = rng.uniform(-1.5, 1.5, (40, 2))
    ax.scatter(pts[:, 0], pts[:, 1], 0.25 * (pts[:, 0]**2 - pts[:, 1]**2) + 0.02,
               s=4, color="#1f3f7a")
    ax.scatter([0], [0], [0.03], s=30, color="black", marker="*")
    ax.text(0.05, 0.05, 0.25, r"$s_0$", fontsize=9)
    ax.set_xlabel(r"$\mathcal{D}_{n,n}$", labelpad=-8)
    ax.set_ylabel("", labelpad=-8)
    ax.set_zlabel("", labelpad=-8)
    ax.set_xticks([]); ax.set_yticks([]); ax.set_zticks([])
    ax.view_init(elev=32, azim=-55)
    ax.set_title(r"$\Sigma_F$: dense, a countable union of closed strata,"
                 "\n" r"either all of $\mathcal{D}_{n,n}$ or meagre", fontsize=10)
    save(fig, "fig_locus")


def fig_eigen():
    """How K^x acts on the Hodge classes of a very general abelian 2n-fold of
    Weil type: eta^k carries the character N(tau)^k, the two Weil classes the
    character tau^(2n) through the K-structure of the Weil line; the two
    differ (tau^(2n) is not even rational), so an N^n-eigenclass in degree 2n
    is a multiple of eta^n."""
    n = 3
    fig = plt.figure(figsize=(7.0, 3.6))
    ax = fig.add_subplot(111, projection="3d")
    ks = np.arange(0, 2 * n + 1)
    for k in ks:
        ax.bar3d(k - 0.3, 0, 0, 0.6, 0.6, 1, color="#9fb4d8", alpha=0.9)
    ax.bar3d(n - 0.3, 1.2, 0, 0.6, 0.6, 1, color="#c0504d", alpha=0.9)
    ax.bar3d(n - 0.3, 2.0, 0, 0.6, 0.6, 1, color="#c0504d", alpha=0.9)
    ax.text(n, 1.6, 1.25, r"character $\tau^{2n}$", fontsize=9, ha="center")
    ax.text(1.0, 0.3, 1.25, r"character $N(\tau)^{k}$", fontsize=9, ha="center")
    ax.set_xlabel(r"degree $2k$", labelpad=4)
    ax.set_yticks([0.3, 1.5, 2.3])
    ax.set_yticklabels([r"$\eta^k$", r"$\omega_1$", r"$\omega_2$"], fontsize=9)
    ax.set_zticks([])
    ax.set_xticks(ks)
    ax.set_xticklabels([str(2 * k) for k in ks], fontsize=9)
    ax.view_init(elev=28, azim=-60)
    ax.set_title(r"Hodge classes of a very general Weil $2n$-fold, $n=3$:"
                 "\n" r"$\eta^n$ and the Weil line carry different characters", fontsize=10)
    save(fig, "fig_eigen")


def fig_graph():
    """The closure graph of statements, drawn in three dimensions: the
    rule set of Section III (the same list is checked in lean/HodgeClosure.lean).
    A joint arrow from two statements means that both are needed."""
    from mpl_toolkits.mplot3d import proj3d
    fig = plt.figure(figsize=(7.0, 3.1))
    ax = fig.add_subplot(111, projection="3d")
    P = {"HC": (0.0, 0.0, 2.4), "F3": (-3.2, 0.4, 1.4), "F2": (-1.2, -0.6, 1.75),
         "F3'": (1.6, -0.6, 0.9), "M": (3.2, 0.4, 1.4), "AB": (-2.2, 0.6, 0.65),
         "L": (-3.2, -0.4, -0.1), "V": (3.2, -0.4, -0.1)}
    single = [("F3", "HC"), ("HC", "F3"), ("HC", "F2"), ("HC", "F3'"),
              ("HC", "M"), ("F2", "AB"), ("AB", "F2"), ("L", "AB"), ("V", "AB")]
    joint = [(("AB", "F3'"), "HC", 0.55), (("L", "M"), "HC", 0.25)]
    def arrow(pa, pb, col, lw):
        d = pb - pa; L = np.linalg.norm(d); u = d / L
        pa, pb = pa + 0.22 * u, pb - 0.22 * u
        ax.quiver(*pa, *(pb - pa), arrow_length_ratio=0.9 / (L - 0.44) * 0.25,
                  color=col, lw=lw)
    for a, b in single:
        arrow(np.array(P[a]), np.array(P[b]), "#444444", 0.9)
    for (a, b), c, t in joint:
        pa, pb, pc = np.array(P[a]), np.array(P[b]), np.array(P[c])
        m = pa + t * (pb - pa)
        for q in (pa, pb):
            ax.plot([q[0], m[0]], [q[1], m[1]], [q[2], m[2]], color="#7a1f1f", lw=1.1)
        ax.scatter(*m, s=14, color="#7a1f1f")
        arrow(m, pc, "#7a1f1f", 1.1)
    for name, p in P.items():
        sc = ax.scatter(*p, s=200, color="#f2c0bd" if name in ("F2", "F3'")
                        else "#dfe7f2", edgecolor="black", zorder=5)
        sc.set_clip_on(False)
    ax.set_xlim(-3.9, 3.9); ax.set_ylim(-1.2, 1.2); ax.set_zlim(-0.3, 2.7)
    ax.set_axis_off(); ax.set_box_aspect((3.4, 1.0, 1.25), zoom=1.5)
    ax.view_init(elev=14, azim=-84)
    fig.canvas.draw()
    off = {"HC": (0, 14), "F3": (-15, 5), "F2": (-15, 5), "F3'": (19, 7),
           "M": (15, 5), "L": (-14, -5), "AB": (-4, -16), "V": (14, -5)}
    for name, p in P.items():
        x, y, _ = proj3d.proj_transform(*p, ax.get_proj())
        ax.annotate(name, (x, y), xycoords="data", textcoords="offset points",
                    xytext=off[name], ha="center", va="center", fontsize=10,
                    annotation_clip=False)
    ax.set_title("The closure graph: HC $\\Leftrightarrow$ (F2) $\\wedge$ (F3$'$)",
                 fontsize=10)
    save(fig, "fig_graph")


def fig_chain():
    """The chain of Theorem A for Q(sqrt 6): X' with an order-3 symplectic
    automorphism, its quotient Y (Hodge isometric to a surface Y' with a
    Nikulin involution), and the quotient Z; the multipliers 3, 1, 2 compose
    to 6, the square of the real multiplication."""
    fig = plt.figure(figsize=(7.0, 3.6))
    ax = fig.add_subplot(111, projection="3d")
    def surf(cx, cy, cz, col, k):
        u = np.linspace(0, 2 * np.pi, 40); v = np.linspace(0, 2 * np.pi, 20)
        U, V = np.meshgrid(u, v)
        R, r = 0.55, 0.22 + 0.04 * k
        X = cx + (R + r * np.cos(V)) * np.cos(U)
        Y = cy + (R + r * np.cos(V)) * np.sin(U)
        Z = cz + r * np.sin(V) * (1 + 0.3 * np.cos(k * U))
        ax.plot_surface(X, Y, Z, color=col, alpha=0.85, linewidth=0)
    surf(0, 0, 2.0, "#9fb4d8", 3); surf(2.2, 0, 1.0, "#c9d9b3", 1)
    surf(4.4, 0, 0.0, "#f2c0bd", 2)
    ax.text(0, 0, 1.1, r"$X'$, $\sigma$ of order 3", ha="center", fontsize=9)
    ax.text(2.2, 0, 0.1, r"$Y\cong Y'$, $\iota$ Nikulin", ha="center", fontsize=9)
    ax.text(4.4, 0, -0.9, r"$Z$", ha="center", fontsize=9)
    ax.quiver(0.75, 0, 1.85, 0.7, 0, -0.6, arrow_length_ratio=0.2, color="black", lw=0.9)
    ax.quiver(2.95, 0, 0.85, 0.7, 0, -0.6, arrow_length_ratio=0.2, color="black", lw=0.9)
    ax.text(1.55, 0, 2.05, r"$\deg 3$", fontsize=9, ha="center")
    ax.text(3.75, 0, 1.05, r"$\deg 2$", fontsize=9, ha="center")
    ax.text2D(0.5, 0.04, r"multiplier $3\cdot1\cdot2=6=e^{2}$", ha="center", fontsize=9, transform=ax.transAxes)
    ax.set_xlim(-1, 5.4); ax.set_ylim(-1.2, 1.2); ax.set_zlim(-1.6, 3.2)
    ax.set_axis_off(); ax.set_box_aspect((3.0, 1.1, 2.2), zoom=1.3); ax.view_init(elev=12, azim=-90)
    ax.set_title(r"Theorem A for $e=\sqrt{6}$: a chain of two symplectic quotients",
                 fontsize=10)
    save(fig, "fig_chain")


def fig_hankel():
    """The lower bound r(gamma) = (4+rho) n^2 - 2n for dim Ext^2 of an object
    whose Chern character has the polarised shape, against n and the Hankel
    rank rho; the markers are the two product cases, n = 3 and n = 4 with
    rho = 3 (57 and 104), and the proved bounds 69 and 640 on E_0^6, E_0^8."""
    fig = plt.figure(figsize=(7.0, 3.6))
    ax = fig.add_subplot(111, projection="3d")
    for rho, col in [(1, "#dfe7f2"), (2, "#9fb4d8"), (3, "#c0504d")]:
        for n in range(2, 7):
            ax.bar3d(n - 0.3, rho - 0.3, 0, 0.6, 0.6, (4 + rho) * n * n - 2 * n,
                     color=col, alpha=0.9)
    ax.text(3, 3, 70, "57", fontsize=9, ha="center")
    ax.text(4, 3, 118, "104", fontsize=9, ha="center")
    ax.set_xlabel(r"$n$", labelpad=2); ax.set_ylabel(r"Hankel rank $\rho$", labelpad=2)
    ax.set_zlabel(r"$r(\gamma)$", labelpad=2)
    ax.set_xticks(range(2, 7)); ax.set_yticks([1, 2, 3])
    ax.tick_params(labelsize=7)
    ax.set_box_aspect((1.6, 1.0, 1.0), zoom=1.1); ax.view_init(elev=24, azim=-58)
    ax.set_title(r"$r(\gamma)=(4+\rho)n^{2}-2n$: the rank the criterion demands",
                 fontsize=10)
    save(fig, "fig_hankel")


def fig_product():
    """The product locus inside the polarised Weil domain: the tangent space
    of the product locus has dimension m^2 + m'^2 and the n^2 - m^2 - m'^2
    mixed directions obstruct every exterior product; the object of Section
    VI has first-order Hodge locus the whole tangent space."""
    fig = plt.figure(figsize=(7.0, 3.6))
    ax = fig.add_subplot(111, projection="3d")
    u = np.linspace(-1.5, 1.5, 40); v = np.linspace(-1.5, 1.5, 40)
    U, V = np.meshgrid(u, v)
    ax.plot_surface(U, V, 0.15 * (U**2 + V**2), color="#dfe7f2", alpha=0.7,
                    linewidth=0)
    t = np.linspace(-1.4, 1.4, 60)
    ax.plot(t, 0 * t, 0.15 * t**2 + 0.01, color="#1f3f7a", lw=2.0)
    ax.scatter([0], [0], [0.02], s=40, color="black", marker="*")
    ax.quiver(0, 0, 0.02, 1.3, 0, 0, color="#1f3f7a", arrow_length_ratio=0.15, lw=1.6)
    ax.quiver(0, 0, 0.02, 0, 1.3, 0, color="#c0504d", arrow_length_ratio=0.15, lw=1.6)
    ax.text2D(0.66, 0.16, r"$T$(product locus), $m^{2}+m'^{2}$", fontsize=9, ha="left", color="#1f3f7a", transform=ax.transAxes)
    ax.text2D(0.30, 0.78, r"mixed directions, $n^{2}-m^{2}-m'^{2}$", fontsize=9,
            color="#c0504d", ha="center", transform=ax.transAxes)
    ax.text2D(0.5, 0.06, r"$A\times A'$", fontsize=10, ha="center", transform=ax.transAxes)
    ax.set_xlim(-1.6, 1.6); ax.set_ylim(-1.6, 1.6)
    ax.set_axis_off(); ax.set_box_aspect((2.4, 2.4, 1.2), zoom=1.2); ax.view_init(elev=28, azim=-60)
    ax.set_title(r"$\mathcal{D}_{n,n}$ near a product point: 4 (resp. 8) mixed"
                 "\n" r"directions obstruct every $F\boxtimes G'$", fontsize=10)
    save(fig, "fig_product")


def fig_link():
    """The sixfold link: the Mumford fourfold X (twice) and the abelian
    sixfold Z_K over the same Shimura curve, and the Hodge class xi in
    H^1(X) x H^1(X) x H^2(Z_K) that identifies the two copies of T."""
    fig = plt.figure(figsize=(7.0, 3.6))
    ax = fig.add_subplot(111, projection="3d")
    s = np.linspace(-1.5, 1.5, 100)
    ax.plot(s, 0.3 * np.sin(2 * s), 0 * s, color="black", lw=1.2)
    ax.text(1.6, 0.3 * np.sin(3.0), 0, r"$C$", fontsize=10)
    def fibre(x0, z0, col, lab):
        th = np.linspace(0, 2 * np.pi, 60)
        ax.plot(x0 + 0 * th, 0.3 * np.sin(2 * x0) + 0.35 * np.cos(th),
                z0 + 0.35 * np.sin(th), color=col, lw=1.6)
        ax.text(x0, 0.3 * np.sin(2 * x0) + 0.5, z0 + 0.55, lab, fontsize=9,
                ha="center")
    fibre(-0.9, 1.2, "#1f3f7a", r"$X_t$"); fibre(0.0, 1.2, "#1f3f7a", r"$X_t$")
    fibre(0.9, 1.2, "#7a1f1f", r"$Z_{K,t}$")
    for x0 in (-0.9, 0.0, 0.9):
        ax.plot([x0, x0], [0.3 * np.sin(2 * x0)] * 2, [0, 0.85], color="grey", lw=0.6)
    ax.plot([-0.9, 0.0, 0.9], [0.3 * np.sin(-1.8) - 0.35, 0.3 * np.sin(0) - 0.35,
            0.3 * np.sin(1.8) - 0.35], [1.2, 1.2, 1.2], color="#2e7d32", lw=1.4)
    ax.text2D(0.5, 0.06, r"$\xi_t\in H^{1}(X)\otimes H^{1}(X)\otimes H^{2}(Z_K)$ (green), flat along $C$",
            fontsize=9, ha="center", color="#2e7d32", transform=ax.transAxes)
    ax.text2D(0.5, 0.93, r"$\xi=m_e\circ\iota\colon\ T_X(-1)\to T_Z$", fontsize=10, ha="center", transform=ax.transAxes)
    ax.set_xlim(-1.8, 1.8); ax.set_ylim(-1.2, 1.2); ax.set_zlim(-0.2, 1.9)
    ax.set_axis_off(); ax.set_box_aspect((3.0, 1.4, 1.6), zoom=1.3); ax.view_init(elev=22, azim=-70)
    ax.set_title("The sixfold link over the Shimura curve", fontsize=10)
    save(fig, "fig_link")


def fig_fricke():
    """The Fricke families of Theorem V.8: over the modular curve X_0(N) with
    Fricke coordinate t, the involution w(t) = N^k/t exchanges the cusps 0 and
    infinity and the two elliptic points e_1, e_2; the twist X_p at the pair
    {p, N^k/p} is carried to itself by the fibrewise isogeny f of degree N,
    and f^* is the real multiplication by sqrt N on the transcendental
    lattice of rank 6."""
    fig = plt.figure(figsize=(7.0, 3.6))
    ax = fig.add_subplot(111, projection="3d")
    # the base P^1_t as a line, with the special points
    ts = np.linspace(-0.2, 4.2, 50)
    ax.plot(ts, 0 * ts, 0 * ts, color="black", lw=1.0)
    pts = {0.0: r"$0$", 4.0: r"$\infty$", 1.2: r"$e_1$", 2.8: r"$e_2$",
           0.6: r"$p$", 3.4: r"$N^{k}/p$"}
    for x, lab in pts.items():
        ax.scatter([x], [0], [0], color="black", s=10)
        ax.text(x, 0, -0.42, lab, fontsize=9, ha="center", va="top")
    # the Fricke involution as arcs under the base
    def arc(x0, x1, depth, col):
        u = np.linspace(0, np.pi, 40)
        ax.plot((x0 + x1) / 2 + (x1 - x0) / 2 * np.cos(u), 0 * u, -depth * np.sin(u), color=col, lw=0.8, ls="--")
    arc(0.0, 4.0, 1.3, "#555555"); arc(1.2, 2.8, 0.6, "#555555"); arc(0.6, 3.4, 0.95, "#b03a2e")
    ax.text(2.0, 0, -1.55, r"$w(t)=N^{k}/t$", fontsize=9, ha="center", color="#555555")
    # the surface X_p: fibres over the base drawn as a tube, with two tori marked
    def tube(x0, x1, cz, col):
        u = np.linspace(x0, x1, 40); v = np.linspace(0, 2 * np.pi, 20)
        U, V = np.meshgrid(u, v)
        r = 0.28 + 0.05 * np.sin(3 * U)
        ax.plot_surface(U, r * np.cos(V), cz + r * np.sin(V), color=col, alpha=0.75, linewidth=0)
    tube(0.1, 3.9, 1.6, "#9fb4d8")
    for x, k in ((0.6, 1), (3.4, 1)):
        u = np.linspace(0, 2 * np.pi, 40); v = np.linspace(0, 2 * np.pi, 20)
        U, V = np.meshgrid(u, v)
        R, r = 0.42, 0.14
        X = x + r * np.sin(V) * 0.6
        Y = (R + r * np.cos(V)) * np.cos(U)
        Z = 1.6 + (R + r * np.cos(V)) * np.sin(U)
        ax.plot_surface(X, Y, Z, color="#f2c0bd", alpha=0.9, linewidth=0)
    ax.text(0.6, 0, 2.35, r"$\mathrm{I}_0^{*}$", fontsize=9, ha="center")
    ax.text(3.4, 0, 2.35, r"$\mathrm{I}_0^{*}$", fontsize=9, ha="center")
    ax.text(2.0, 0, 2.25, r"$X_p=X_{p,N^{k}/p}$", fontsize=9, ha="center")
    # the self-isogeny
    u = np.linspace(0, np.pi, 40)
    ax.plot(2.0 + 1.6 * np.cos(u), 0 * u, 2.6 + 0.5 * np.sin(u), color="#b03a2e", lw=1.0)
    ax.quiver(3.55, 0, 2.65, 0.05, 0, -0.1, arrow_length_ratio=0.9, color="#b03a2e", lw=1.0)
    ax.text(2.0, 0, 3.3, r"$f$, degree $N$: $f^{*}=\pm\sqrt{N}$ on $T(X_p)$, rank $6$", fontsize=9, ha="center", color="#b03a2e")
    ax.set_xlim(-0.3, 4.3); ax.set_ylim(-1.2, 1.2); ax.set_zlim(-1.6, 3.6)
    ax.set_axis_off(); ax.set_box_aspect((3.0, 1.2, 2.4), zoom=1.35); ax.view_init(elev=10, azim=-90)
    ax.set_title(r"The family $\mathfrak{A}_N$, $N\in\{5,7\}$: twists at a pair exchanged by $w$",
                 fontsize=10)
    save(fig, "fig_fricke")


def _lab(ax, x, y, z, text, dx=0, dy=0, **kw):
    """Place a label at a 3D point through the 2D projection, so that
    offsets are in points and labels never overlap the plotted geometry."""
    from mpl_toolkits.mplot3d import proj3d
    X, Y, _ = proj3d.proj_transform(x, y, z, ax.get_proj())
    kw.setdefault("fontsize", 9)
    return ax.annotate(text, (X, Y), xytext=(dx, dy), textcoords="offset points",
                       ha=kw.pop("ha", "center"), va=kw.pop("va", "center"),
                       annotation_clip=False, **kw)


def fig_zeta9():
    """Theorem thm:zeta9: the two-dimensional period domain of the twelve-
    dimensional space with real multiplication by Q(zeta_7)^+ or Q(zeta_9)^+, the image of
    the dihedral family as a shaded patch, the curves where an F-line becomes
    algebraic, the point of Mumford type, and the rational isometry that
    moves it into the patch."""
    fig = plt.figure(figsize=(7.0, 3.5))
    ax = fig.add_subplot(111, projection="3d")
    ax.computed_zorder = False
    u = np.linspace(-1.8, 1.8, 120); v = np.linspace(-1.2, 1.2, 90)
    U, V = np.meshgrid(u, v)
    f = lambda x, y: 0.18 * (x**2 - 1.4 * y**2) + 0.1 * np.sin(1.3 * x)
    Z = f(U, V)
    inpatch = ((U - 1.0) / 0.55)**2 + ((V + 0.15) / 0.55)**2 <= 1
    fc = np.empty(U.shape + (4,))
    fc[...] = matplotlib.colors.to_rgba("#dde5f0", 1.0)
    fc[inpatch] = matplotlib.colors.to_rgba("#f0c78a", 1.0)
    ax.plot_surface(U, V, Z, facecolors=fc, linewidth=0, shade=True, antialiased=False, zorder=1)
    rng = np.random.default_rng(9)
    for k in range(7):
        t = np.linspace(-1.1, 1.1, 90)
        a = rng.uniform(-1.5, 1.5); b = rng.uniform(-1, 1)
        x = a + 0.4 * np.sin(1.7 * t + b); y = t
        ax.plot(x, y, f(x, y) + 0.02, color="#7a1f1f", lw=0.9, zorder=3)
    x0, y0 = -1.1, -0.45; x1, y1 = 1.0, -0.1
    ax.scatter([x0, x1], [y0, y1], [f(x0, y0) + 0.04, f(x1, y1) + 0.04], s=48, color="black",
               marker="*", depthshade=False, zorder=5)
    t = np.linspace(0, 1, 60)
    xs = x0 + (x1 - x0) * t; ys = y0 + (y1 - y0) * t
    zs = f(xs, ys) + 0.45 * np.sin(np.pi * t) + 0.04
    ax.plot(xs, ys, zs, color="#1f3f7a", lw=1.4, zorder=4)
    ax.quiver(xs[-2], ys[-2], zs[-2], x1 - xs[-2], y1 - ys[-2], f(x1, y1) + 0.04 - zs[-2],
              arrow_length_ratio=0.9, color="#1f3f7a", lw=1.4, zorder=4)
    ax.set_xlim(-1.9, 1.9); ax.set_ylim(-1.3, 1.3); ax.set_zlim(-0.5, 1.0)
    ax.set_axis_off(); ax.set_box_aspect((3.0, 1.8, 1.1), zoom=1.3); ax.view_init(elev=34, azim=-58)
    fig.canvas.draw()
    _lab(ax, x0, y0, f(x0, y0), r"$[S_{\lambda}]$", dx=-8, dy=-16)
    _lab(ax, x1, y1, f(x1, y1), r"$g\cdot[S_{\lambda}]$", dx=34, dy=4)
    _lab(ax, xs[30], ys[30], zs[30], r"$x\mapsto axg$, $(a,g)\in Q^{1}\times Q^{1}$", dy=14, color="#1f3f7a")
    _lab(ax, 1.0, -0.7, f(1.0, -0.7), r"$U$, image of the dihedral family", dx=36, dy=-24, color="#7a4a10")
    _lab(ax, -1.75, 1.1, f(-1.75, 1.1), r"$\mathcal{D}_{T_{12}}$", dx=-10, dy=12)
    _lab(ax, -1.2, -1.2, f(-1.2, -1.2), r"loci where an $F$-line $N$ is algebraic", dx=-30, dy=-44, color="#7a1f1f")
    ax.set_title(r"Real multiplication by $\mathbb{Q}(\zeta_7)^{+}$ or $\mathbb{Q}(\zeta_9)^{+}$: moving the surface of Mumford type into the dihedral family",
                 fontsize=10)
    save(fig, "fig_zeta9")


def fig_surgery():
    """Proposition prop:surgery: four scenes, each two varieties drawn as
    shaded solids with their defect as a bar; the arrows are the four devices
    and the bars show that none of them lowers the defect."""
    from matplotlib.patches import Ellipse, FancyArrowPatch, Rectangle
    fig, ax = plt.subplots(figsize=(7.0, 2.9))
    cols = ["#9fb4d4", "#d98f8a", "#8fbf8a", "#d7b36a"]
    xs = [1.4, 4.4, 7.4, 10.4]
    names = ["blow-up\n" r"$\tilde X=\mathrm{Bl}_Z X\to X$", "dominating map\n" r"$Y\to X$",
             "derived equivalence\n" r"$D(X)\simeq D(X')$", "degeneration\n" r"$X_t\leadsto X_0$"]
    heights = [(0.9, 1.4), (0.9, 1.5), (0.9, 0.9), (0.9, 0.0)]
    toplab = [(r"$\delta(X)$", r"$\delta(X)+\delta(Z)$"), (r"$\delta(X)$", r"$\delta(Y)\geq\delta(X)$"),
              (r"$\Sigma_p\,\delta^{p}(X)$", r"$\Sigma_p\,\delta^{p}(X')$"), (r"$\delta(X_t)$", "class lost")]

    def solid(cx, cy, c):
        ax.add_patch(Ellipse((cx, cy), 1.3, 0.9, facecolor=c, edgecolor="none"))
        ax.add_patch(Ellipse((cx - 0.15, cy + 0.12), 0.75, 0.42, facecolor="white", alpha=0.35, edgecolor="none"))
        ax.add_patch(Ellipse((cx, cy - 0.5), 1.3, 0.28, facecolor="black", alpha=0.08, edgecolor="none"))

    for cx, c, (h0, h1), (l0, l1), nm in zip(xs, cols, heights, toplab, names):
        for dx, h, lab in ((-0.8, h0, l0), (0.8, h1, l1)):
            solid(cx + dx, 0.0, c)
            if h > 0:
                ax.add_patch(Rectangle((cx + dx - 0.12, 0.65), 0.24, h, facecolor="#7a1f1f", edgecolor="none"))
            ax.text(cx + dx, 0.75 + h + 0.12, lab, ha="center", va="bottom", fontsize=8.5)
        ax.add_patch(FancyArrowPatch((cx - 0.1, 0.0), (cx + 0.1, 0.0), arrowstyle="-|>", mutation_scale=10, lw=1.0, color="black"))
        ax.text(cx, -0.95, nm, ha="center", va="top", fontsize=8.5)
    ax.add_patch(Ellipse((xs[0] + 0.8, 0.05), 0.4, 0.16, facecolor="none", edgecolor="#1f3f7a", lw=1.2))
    ax.text(xs[0] + 0.8, 0.28, r"$E\to Z$", ha="center", va="bottom", fontsize=8, color="#1f3f7a")
    ax.set_xlim(0, 11.9); ax.set_ylim(-1.9, 2.9); ax.set_aspect("equal"); ax.set_axis_off()
    ax.set_title(r"The defect $\delta=\dim\mathrm{Hdg}/\mathrm{Alg}$ never drops: blow-up, domination, derived equivalence, degeneration",
                 fontsize=10)
    save(fig, "fig_surgery")


def fig_cubicstop():
    """Proposition prop:cubicstop: the three places where the dihedral mechanism
    stops. Left: the Mumford algebras over F = Q(zeta_7)^+ or Q(zeta_9)^+ as a
    row of discs; a rank-twelve family carries only D_infinity. Middle: the
    four-dimensional period domain of the rank-eighteen family drawn as a box,
    the image of the family as a threefold (a surface in the picture) and the
    Shimura curves of the surfaces of Mumford type for the other algebras, which
    the threefold is not known to meet. Right: the finite groups acting on the
    base P^1 and the fields they produce."""
    from matplotlib.patches import Circle, FancyArrowPatch, Rectangle, FancyBboxPatch
    fig = plt.figure(figsize=(7.2, 3.9))
    gs = fig.add_gridspec(1, 3, width_ratios=[0.95, 1.5, 0.95], wspace=0.02)
    # left panel: algebras over F
    ax = fig.add_subplot(gs[0, 0]); ax.set_axis_off()
    ax.set_xlim(0, 10); ax.set_ylim(0, 10)
    ax.text(5, 9.3, r"Mumford algebras $D$ over $F$", ha="center", fontsize=9)
    labels = [r"$D_{\infty}$", r"$D_{13}$", r"$D_{29}$", r"$D_{41}$", r"$\cdots$"]
    from matplotlib.patches import Ellipse
    for k, lab in enumerate(labels):
        cx = 1.3 + 2.15 * k
        if k < 4:
            col = "#f0c78a" if k == 0 else "#dde5f0"
            ax.add_patch(Ellipse((cx, 6.3), 2.0, 1.25, facecolor=col, edgecolor="#333333", lw=0.8))
        ax.text(cx, 6.3, lab, ha="center", va="center", fontsize=8.5)
    ax.text(5, 4.6, r"ramified at two real places, and at", ha="center", fontsize=8)
    ax.text(5, 3.9, r"two places above a split prime $p$", ha="center", fontsize=8)
    ax.add_patch(FancyArrowPatch((1.2, 2.9), (1.2, 2.1), arrowstyle="-|>", mutation_scale=9, lw=1.0, color="#7a4a10"))
    ax.text(5, 1.75, r"rank-twelve family, disc$\,\Phi$ a square,", ha="center", va="center", fontsize=8, color="#7a4a10")
    ax.text(5, 1.15, r"only $D_{\infty}$ is reached", ha="center", va="center", fontsize=8, color="#7a4a10")
    ax.text(5, 0.3, "(i)", ha="center", fontsize=9)
    # middle panel: the four-dimensional domain of the rank-eighteen family
    ax = fig.add_subplot(gs[0, 1], projection="3d"); ax.computed_zorder = False; ax.patch.set_alpha(0)
    u = np.linspace(-1, 1, 40); v = np.linspace(-1, 1, 40); U, V = np.meshgrid(u, v)
    Z = 0.25 * U - 0.35 * V**2 + 0.1
    ax.plot_surface(U, V, Z, color="#f0c78a", alpha=0.95, linewidth=0, shade=True, zorder=1)
    # box edges
    for sgn in [(-1, -1), (-1, 1), (1, -1), (1, 1)]:
        ax.plot([sgn[0]] * 2, [sgn[1]] * 2, [-1, 1], color="#999999", lw=0.6, zorder=0)
    for z in (-1, 1):
        ax.plot([-1, 1, 1, -1, -1], [-1, -1, 1, 1, -1], [z] * 5, color="#999999", lw=0.6, zorder=0)
    t = np.linspace(-0.95, 0.95, 60)
    curves = [(0.55 * t, -0.6 + 0.2 * t, 0.65 - 0.4 * t**2), (-0.7 + 0.1 * t, 0.5 * t, -0.55 + 0.3 * t),
              (0.6 + 0.2 * t, 0.7 * t, 0.85 - 0.5 * t)]
    for cx, cy, cz in curves:
        ax.plot(cx, cy, cz, color="#7a1f1f", lw=1.1, zorder=3)
    ax.scatter([0.35], [-0.6], [0.65 - 0.4 * 0.35**2 / 0.55**2 * 0.55**2], s=36, color="black", marker="*", depthshade=False, zorder=5)
    ax.set_xlim(-1.1, 1.1); ax.set_ylim(-1.1, 1.1); ax.set_zlim(-1.1, 1.1)
    ax.set_axis_off(); ax.set_box_aspect((1, 1, 1), zoom=0.85); ax.view_init(elev=22, azim=-55)
    fig.canvas.draw()
    _lab(ax, 0, 0, 1.0, r"$\mathcal{D}_{T_{18}}$, dimension four", dy=22)
    _lab(ax, 0, 0, -1.0, "$U$, image of the family,\ndimension three", dy=-24, fontsize=8, color="#7a4a10")
    _lab(ax, 0, 0, -1.0, "Shimura curves of $(F,D)$,\nnot known to meet $U$", dy=-48, fontsize=8, color="#7a1f1f")
    _lab(ax, 0, 0, -1.0, "(ii)", dy=-66)
    # right panel: finite groups on P^1 and their fields
    ax = fig.add_subplot(gs[0, 2]); ax.set_axis_off()
    ax.set_xlim(0, 10); ax.set_ylim(0, 10)
    ax.text(5, 9.3, r"finite groups acting on $\mathbb{P}^{1}$", ha="center", fontsize=9)
    rows = [(r"$C_{m}$", r"$\mathbb{Q}(\zeta_{m})$"), (r"$D_{m}$", r"$\mathbb{Q}(\zeta_{m})^{+}$"),
            (r"$A_{4}$", r"$\mathbb{Q},\ \mathbb{Q}(\sqrt{-3})$"), (r"$S_{4}$", r"$\mathbb{Q}$"), (r"$A_{5}$", r"$\mathbb{Q},\ \mathbb{Q}(\sqrt{5})$")]
    for k, (g, f) in enumerate(rows):
        y = 7.6 - 1.25 * k
        col = "#f0c78a" if k == 1 else "#dde5f0"
        ax.add_patch(FancyBboxPatch((0.6, y - 0.42), 2.2, 0.84, boxstyle="round,pad=0.05", facecolor=col, edgecolor="#333333", lw=0.7))
        ax.text(1.7, y, g, ha="center", va="center", fontsize=8.5)
        ax.add_patch(FancyArrowPatch((3.0, y), (4.1, y), arrowstyle="-|>", mutation_scale=8, lw=0.8, color="black"))
        ax.text(4.4, y, f, ha="left", va="center", fontsize=8.5)
    ax.text(5, 1.3, r"cubic only for $D_{7},D_{9},D_{14},D_{18}$", ha="center", fontsize=8, color="#7a4a10")
    ax.text(5, 0.4, "(iii)", ha="center", fontsize=9)
    fig.suptitle(r"Where the dihedral mechanism stops: finitely ramified algebras, the threefold in $\mathcal{D}_{T_{18}}$, and the fields of finite groups on $\mathbb{P}^{1}$", fontsize=9.5, y=0.99)
    save(fig, "fig_cubicstop")


def fig_cmpoint():
    """Appendix A: the three Weil surfaces B_j with the four curves C_zeta, the dimensions of the
    Ext groups between two twists of one threefold, and the closed chains of Proposition VI.9."""
    fig = plt.figure(figsize=(7.6, 3.5))
    gs = fig.add_gridspec(1, 3, width_ratios=[1.2, 1.0, 1.1], wspace=0.12)
    # (a) three surfaces, each a square torus fundamental domain, with the four curves u + zeta v = 0
    ax = fig.add_subplot(gs[0, 0], projection="3d")
    ax.computed_zorder = False
    cols = {"1": "#7a1f1f", "i": "#1f3f7a", "-1": "#2f6f2f", "-i": "#7a4a10"}
    for j, y0 in enumerate([0.0, 1.6, 3.2]):
        sq = [(0, y0, 0), (1, y0, 0), (1, y0, 1), (0, y0, 1)]
        ax.add_collection3d(Poly3DCollection([sq], facecolor="#dde5f0", edgecolor="#555555",
                                             linewidth=0.7, alpha=0.95, zorder=1))
        t = np.linspace(0, 1, 60)
        # the curves u = -zeta v drawn on the real slice: zeta = +-1 give the two diagonals,
        # zeta = +-i the curves closing after a half turn (drawn as the mid-lines)
        ax.plot(t, y0 + 0 * t, 1 - t, color=cols["1"], lw=1.3, zorder=3)
        ax.plot(t, y0 + 0 * t, t, color=cols["-1"], lw=1.3, zorder=3)
        ax.plot(t, y0 + 0 * t, 0.5 + 0 * t, color=cols["i"], lw=1.3, zorder=3)
        ax.plot(0.5 + 0 * t, y0 + 0 * t, t, color=cols["-i"], lw=1.3, zorder=3)
        ax.scatter([0.5], [y0], [0.5], s=14, color="black", zorder=4, depthshade=False)
    ax.set_xlim(0, 1); ax.set_ylim(-0.2, 4.4); ax.set_zlim(0, 1)
    ax.set_axis_off(); ax.set_box_aspect((1.0, 2.6, 1.0), zoom=1.25); ax.view_init(elev=22, azim=-62)
    fig.canvas.draw()
    for j, y0 in enumerate([0.0, 1.6, 3.2]):
        _lab(ax, 0.5, y0, 1.02, r"$B_{%d}=E_{0}^{2}$" % (j + 1), dy=9)
    _lab(ax, 1.0, 0.0, 0.0, r"$C_{1}$", dx=10, dy=-6, color=cols["1"])
    _lab(ax, 0.0, 0.0, 0.0, r"$C_{-1}$", dx=-14, dy=-8, color=cols["-1"])
    _lab(ax, 1.0, 0.0, 0.5, r"$C_{i}$", dx=10, dy=0, color=cols["i"])
    _lab(ax, 0.5, 0.0, 0.0, r"$C_{-i}$", dx=-14, dy=-6, color=cols["-i"])
    ax.text2D(0.5, -0.01, r"$\sum_{\zeta_1\zeta_2\zeta_3=\pm1}\pm[Z_{\zeta}]=32(\alpha+\bar\alpha)$",
              transform=ax.transAxes, ha="center", va="top", fontsize=8)
    ax.set_title(r"(a) the curves $C_{\zeta}=\ker(u+\zeta v)$ in $B_{j}$", fontsize=9, pad=0)
    # (b) dimensions of Ext^k(O_Z L^a, O_Z L^b)
    ax = fig.add_subplot(gs[0, 1])
    k = np.arange(7)
    d0 = [1, 6, 15, 20, 15, 6, 1]
    d1 = [8, 24, 24, 8, 0, 0, 0]
    dm = [0, 0, 0, 8, 24, 24, 8]
    w = 0.27
    ax.bar(k - w, d0, w, color="#9aa9c2", label=r"$b-a=0$")
    ax.bar(k, d1, w, color="#7a1f1f", label=r"$b-a=1$")
    ax.bar(k + w, dm, w, color="#1f3f7a", label=r"$b-a=-1$")
    for i, v in enumerate(d0):
        ax.text(i - w, v + 0.4, str(v), ha="center", va="bottom", fontsize=6.5, color="#333333")
    ax.set_xticks(k); ax.set_xlabel(r"$k$", labelpad=1)
    ax.set_ylabel(r"$\dim\,\mathrm{Ext}^{k}(\mathcal{O}_Z L^{a},\mathcal{O}_Z L^{b})$", fontsize=8)
    ax.set_ylim(0, 31); ax.legend(fontsize=7, frameon=False, loc="upper left", ncol=3, columnspacing=0.8, handlelength=1.0, bbox_to_anchor=(-0.02, 1.02))
    ax.spines["top"].set_visible(False); ax.spines["right"].set_visible(False)
    ax.tick_params(labelsize=8)
    ax.set_title(r"(b) two twists of one $Z$", fontsize=9)
    # (c) the closed chains
    ax = fig.add_subplot(gs[0, 2]); ax.set_axis_off()
    ax.set_xlim(0, 10); ax.set_ylim(0, 10)
    P = {"k": (2.0, 2.2), "k'": (5.0, 7.6), "k''": (8.0, 2.2)}
    names = {"k": r"$\mathcal{O}_Z L^{k}$", "k'": r"$\mathcal{O}_Z L^{k'}$", "k''": r"$\mathcal{O}_Z L^{k''}$"}
    for key, (x, y) in P.items():
        ax.add_patch(plt.Circle((x, y), 0.95, facecolor="#dde5f0", edgecolor="#333333", lw=0.8))
        ax.text(x, y, names[key], ha="center", va="center", fontsize=8)
    def arrow(a, b, text, col, rad, dx, dy):
        (x1, y1), (x2, y2) = P[a], P[b]
        ax.annotate("", xy=(x2, y2), xytext=(x1, y1),
                    arrowprops=dict(arrowstyle="-|>", color=col, lw=1.2, shrinkA=20, shrinkB=20,
                                    connectionstyle="arc3,rad=%s" % rad))
        ax.text((x1 + x2) / 2 + dx, (y1 + y2) / 2 + dy, text, ha="center", va="center", fontsize=8, color=col)
    arrow("k", "k'", r"$\mathrm{Ext}^{0}$", "#7a1f1f", -0.15, -1.3, 0.3)
    arrow("k'", "k''", r"$\mathrm{Ext}^{0}$", "#7a1f1f", -0.15, 1.3, 0.3)
    arrow("k''", "k", r"$\mathrm{Ext}^{3}=H^{3}(Z,L^{k-k''}|_Z)$", "#1f3f7a", -0.25, 0, -1.3)
    ax.text(5.0, 5.3, r"$0+0+3=3$", ha="center", fontsize=8)
    ax.text(5.0, 4.4, r"a product into $\mathrm{Ext}^{2}$", ha="center", fontsize=8)
    ax.text(5.0, -0.6, r"two pieces: $k_{1}+k_{2}\geq 3$, nothing in $\mathrm{Ext}^{2}$",
            ha="center", fontsize=7.5, color="#333333")
    ax.set_title(r"(c) closed chains, $k<k'<k''$", fontsize=9)
    save(fig, "fig_cmpoint")


def fig_roadmap():
    """Section I: the plan of the paper as a flow chart. The reduction HC <=> (F2) and (F3'), the
    shape of the two loci, and for each statement the constructions of the paper with the step at
    which each one stops."""
    fig, ax = plt.subplots(figsize=(7.4, 3.9))
    ax.set_xlim(0, 100); ax.set_ylim(0, 52); ax.set_axis_off()
    def box(x, y, w, h, text, fc="#dde5f0", ec="#333333", fs=8, lw=0.8, style="round,pad=0.4"):
        ax.add_patch(matplotlib.patches.FancyBboxPatch((x - w / 2, y - h / 2), w, h, boxstyle=style,
                                                       facecolor=fc, edgecolor=ec, linewidth=lw))
        ax.text(x, y, text, ha="center", va="center", fontsize=fs)
    def arr(x1, y1, x2, y2, col="#333333", lw=1.0, rad=0.0):
        ax.annotate("", xy=(x2, y2), xytext=(x1, y1),
                    arrowprops=dict(arrowstyle="-|>", color=col, lw=lw, shrinkA=2, shrinkB=2,
                                    connectionstyle="arc3,rad=%s" % rad))
    red, blue, gold, grey = "#7a1f1f", "#1f3f7a", "#7a4a10", "#555555"
    box(50, 48, 46, 6, r"the Hodge conjecture $\Leftrightarrow$ (F2) $\wedge$ (F3$'$)", fc="#f0e3c0", fs=8.5)
    box(50, 40.5, 56, 5.2, r"the locus of either statement: dense, every CM point, all or meagre", fc="#e8e8e8", fs=8)
    arr(50, 45, 50, 43.1)
    # the two columns
    box(24, 33, 46, 5, r"(F3$'$): every Hodge class comes from abelian varieties" "\n" r"first case: real multiplication of K3 surfaces", fc="#e5ecf6", ec=blue, fs=7.2)
    box(76, 33, 46, 5, r"(F2): the Hodge conjecture for abelian varieties" "\n" r"first case: Weil classes of a product of two fourfolds", fc="#f6e5e5", ec=red, fs=7.2)
    arr(38, 38, 28, 35.6, col=blue); arr(62, 38, 72, 35.6, col=red)
    # F3' constructions
    ys = [25.5, 18.5, 11.5]
    left = [(r"$\sqrt{6}$: chain of two quotients, $3\cdot2$", r"stops: $\sqrt{N}$ needs a map of degree $N$"),
            (r"$\sqrt{5},\sqrt{7}$: Fricke isogenies in families", r"stops: only multiquadratic fields"),
            (r"$\mathbb{Q}(\zeta_7)^{+},\mathbb{Q}(\zeta_9)^{+}$ on Mumford type", r"stops: other cubic fields, other algebras")]
    right = [(r"product object on $A\times A'$, Hankel rank 3", r"stops: Ext of the secant sheaves"),
             (r"CM point $E_0^6$: all Ext groups explicit", r"stops: ranks of Massey products"),
             (r"sixfold link $\xi$ on $X\times X\times Z_K$", r"stops: algebraicity of $\xi$")]
    for (t1, t2), y in zip(left, ys):
        box(24, y, 42, 4.6, t1 + "\n" + t2, fc="white", ec=blue, fs=7.2)
    for (t1, t2), y in zip(right, ys):
        box(76, y, 42, 4.6, t1 + "\n" + t2, fc="white", ec=red, fs=7.2)
    arr(24, 30.5, 24, 27.9, col=blue); arr(24, 23.2, 24, 20.9, col=blue); arr(24, 16.2, 24, 13.9, col=blue)
    arr(76, 30.5, 76, 27.9, col=red); arr(76, 23.2, 76, 20.9, col=red); arr(76, 16.2, 76, 13.9, col=red)
    box(24, 4.5, 46, 4.4, r"proved: HC for $S\times S$ in the dihedral families," "\n" r"and for $S_\lambda\times S_\lambda$ and $S_\lambda^{[2]}$ of Mumford type", fc="#e5ecf6", ec=blue, fs=7.0)
    box(76, 4.5, 46, 4.4, r"proved: what each object does and where it stops;" "\n" r"the defect survives maps, blow-ups, derived equivalences", fc="#f6e5e5", ec=red, fs=7.0)
    arr(24, 9.2, 24, 6.9, col=blue); arr(76, 9.2, 76, 6.9, col=red)
    ax.text(50, 18.5, "both open", ha="center", va="center", fontsize=9, color=grey, rotation=90)
    save(fig, "fig_roadmap")


def fig_extgrid():
    """Appendix A: the least degree k with Ext^k(F_P, F_Q) != 0 for the twelve pieces O_Z L^k,
    O_Z' L^k, L^k (k = 0..3), as a matrix; the two-step and three-step statements of
    Proposition VI.9 are read off from it."""
    import itertools
    TW = range(4)
    pieces = [('Z', k) for k in TW] + [('W', k) for k in TW] + [('L', k) for k in TW]
    def degrees(P, Q):
        (t, a), (u, b) = P, Q
        if P == Q: return set(range(7))
        if t == 'L' and u == 'L': return {0} if b > a else {6}
        if t == 'L' and u != 'L': return {0} if b > a else ({3} if b < a else {0, 1, 2, 3})
        if t != 'L' and u == 'L': return {3} if b > a else ({6} if b < a else {3, 4, 5, 6})
        if t != u: return {3}
        if b > a: return {0, 1, 2, 3}
        return {3, 4, 5, 6}
    n = len(pieces)
    M = np.array([[min(degrees(P, Q)) for Q in pieces] for P in pieces], dtype=float)
    fig, axes = plt.subplots(1, 2, figsize=(7.4, 3.6), gridspec_kw=dict(width_ratios=[1.35, 1.0], wspace=0.5))
    ax = axes[0]
    cmap = matplotlib.colors.ListedColormap(["#7a1f1f", "#c7a0a0", "#e3cfcf", "#dde5f0", "#9aa9c2", "#5f719a", "#1f3f7a"])
    im = ax.imshow(M, cmap=cmap, vmin=-0.5, vmax=6.5)
    labels = [r"$\mathcal{O}_Z L^{%d}$" % k for k in TW] + [r"$\mathcal{O}_{Z'} L^{%d}$" % k for k in TW] + [r"$L^{%d}$" % k for k in TW]
    ax.set_xticks(range(n)); ax.set_yticks(range(n))
    ax.set_xticklabels(labels, fontsize=6.5, rotation=90); ax.set_yticklabels(labels, fontsize=6.5)
    for i in range(n):
        for j in range(n):
            d = sorted(degrees(pieces[i], pieces[j]))
            txt = "%d" % d[0] if len(d) == 1 else ("%d..%d" % (d[0], d[-1]) if i != j else "0..6")
            ax.text(j, i, txt, ha="center", va="center", fontsize=5.5,
                    color="white" if M[i, j] in (0, 6) else "black")
    for p in (3.5, 7.5):
        ax.axhline(p, color="black", lw=0.6); ax.axvline(p, color="black", lw=0.6)
    ax.set_xlabel("to", fontsize=8); ax.set_ylabel("from", fontsize=8)
    ax.set_title(r"(a) degrees $k$ with $\mathrm{Ext}^{k}(\mathcal{F}_P,\mathcal{F}_Q)\neq0$", fontsize=9)
    cb = fig.colorbar(im, ax=ax, ticks=range(7), fraction=0.046, pad=0.03); cb.ax.tick_params(labelsize=7)
    cb.set_label("least degree", fontsize=7)
    # (b) histogram of the total degree of all closed chains of two and of three distinct pieces
    ax = axes[1]
    two = []
    for P, Q in itertools.permutations(pieces, 2):
        two += [k1 + k2 for k1 in degrees(P, Q) for k2 in degrees(Q, P)]
    three = []
    for P, Q, R in itertools.permutations(pieces, 3):
        three += [k1 + k2 + k3 for k1 in degrees(P, Q) for k2 in degrees(Q, R) for k3 in degrees(R, P)]
    bins = np.arange(-0.5, 19.5, 1)
    h2, _ = np.histogram(two, bins); h3, _ = np.histogram(three, bins)
    xs = np.arange(0, 19)
    ax.bar(xs - 0.2, h2, 0.4, color="#1f3f7a", label="two pieces")
    ax.bar(xs + 0.2, h3, 0.4, color="#7a1f1f", label="three pieces")
    ax.axvline(2.5, color="black", lw=0.8, ls="--")
    ax.text(2.3, 0.8, "degree 2 needs\n" r"$\sum k_i=m$", ha="right", va="bottom", fontsize=7)
    ax.annotate("%d at degree 3:\nthree twists of one $Z$" % h3[3], xy=(3.2, h3[3] * 1.3), xytext=(0.2, max(h3) * 3.5),
                fontsize=7, color="#7a1f1f", ha="left", va="top",
                arrowprops=dict(arrowstyle="-|>", color="#7a1f1f", lw=0.8, shrinkB=2))
    ax.set_yscale("log"); ax.set_ylim(0.7, max(h3) * 5)
    ax.set_xticks(range(0, 19, 2)); ax.tick_params(labelsize=7.5)
    ax.set_xlabel(r"total Ext degree $k_1+\dots+k_m$ of a closed chain", fontsize=8)
    ax.set_ylabel("number of chains", fontsize=8)
    ax.legend(fontsize=7, frameon=False, loc="upper right")
    ax.spines["top"].set_visible(False); ax.spines["right"].set_visible(False)
    ax.set_title("(b) closed chains over the twelve pieces", fontsize=9)
    save(fig, "fig_extgrid")


if __name__ == "__main__":
    fig_locus(); fig_eigen(); fig_graph(); fig_chain()
    fig_hankel(); fig_product(); fig_link(); fig_fricke()
    fig_zeta9(); fig_surgery(); fig_cubicstop(); fig_cmpoint(); fig_roadmap(); fig_extgrid()
    print("figures written to", os.path.abspath(OUT))
