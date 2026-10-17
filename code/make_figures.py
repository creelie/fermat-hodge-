"""Figures of the paper: 3D plots drawn with matplotlib.

Run from the repository root:  python3 code/make_figures.py
Writes PDF (vector) and PNG (200 dpi) files to paper/figures/.
"""
import os
import numpy as np
import matplotlib
import matplotlib.colors
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
    dimensional space with real multiplication by Q(zeta_9)^+, the image of
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
    ax.set_title(r"Real multiplication by $\mathbb{Q}(\zeta_9)^{+}$: moving the surface of Mumford type into the dihedral family",
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

if __name__ == "__main__":
    fig_locus(); fig_eigen(); fig_graph(); fig_chain()
    fig_hankel(); fig_product(); fig_link(); fig_fricke()
    fig_zeta9(); fig_surgery()
    print("figures written to", os.path.abspath(OUT))
