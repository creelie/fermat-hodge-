"""Figures of the paper: 3D plots drawn with matplotlib.

Run from the repository root:  python3 code/make_figures.py
Writes PDF (vector) and PNG (200 dpi) files to paper/figures/.
"""
import os
import numpy as np
import matplotlib
matplotlib.use("Agg")
import matplotlib.pyplot as plt
from mpl_toolkits.mplot3d import Axes3D  # noqa: F401
from mpl_toolkits.mplot3d.art3d import Poly3DCollection

OUT = os.path.join(os.path.dirname(__file__), "..", "paper", "figures")
os.makedirs(OUT, exist_ok=True)
plt.rcParams.update({"font.family": "serif", "font.size": 9,
                     "mathtext.fontset": "cm"})


def save(fig, name):
    fig.savefig(os.path.join(OUT, name + ".pdf"), bbox_inches="tight")
    fig.savefig(os.path.join(OUT, name + ".png"), dpi=200, bbox_inches="tight")
    plt.close(fig)


def fig_locus():
    """The period domain of a Weil family as a surface; the algebraic locus
    is a dense countable union of closed strata (curves and points), and the
    dichotomy says it is either everything or meagre."""
    fig = plt.figure(figsize=(3.4, 3.0))
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
                 "\n" r"either all of $\mathcal{D}_{n,n}$ or meagre", fontsize=8)
    save(fig, "fig_locus")


def fig_eigen():
    """How K^x acts on the Hodge classes of a very general abelian 2n-fold of
    Weil type: eta^k carries the character N(tau)^k, the two Weil classes the
    character tau^(2n) through the K-structure of the Weil line; the two
    differ (tau^(2n) is not even rational), so an N^n-eigenclass in degree 2n
    is a multiple of eta^n."""
    n = 3
    fig = plt.figure(figsize=(3.4, 3.0))
    ax = fig.add_subplot(111, projection="3d")
    ks = np.arange(0, 2 * n + 1)
    for k in ks:
        ax.bar3d(k - 0.3, 0, 0, 0.6, 0.6, 1, color="#9fb4d8", alpha=0.9)
    ax.bar3d(n - 0.3, 1.2, 0, 0.6, 0.6, 1, color="#c0504d", alpha=0.9)
    ax.bar3d(n - 0.3, 2.0, 0, 0.6, 0.6, 1, color="#c0504d", alpha=0.9)
    ax.text(n, 1.6, 1.25, r"character $\tau^{2n}$", fontsize=7, ha="center")
    ax.text(1.0, 0.3, 1.25, r"character $N(\tau)^{k}$", fontsize=7, ha="center")
    ax.set_xlabel(r"degree $2k$", labelpad=4)
    ax.set_yticks([0.3, 1.5, 2.3])
    ax.set_yticklabels([r"$\eta^k$", r"$\omega_1$", r"$\omega_2$"], fontsize=7)
    ax.set_zticks([])
    ax.set_xticks(ks)
    ax.set_xticklabels([str(2 * k) for k in ks], fontsize=7)
    ax.view_init(elev=28, azim=-60)
    ax.set_title(r"Hodge classes of a very general Weil $2n$-fold, $n=3$:"
                 "\n" r"$\eta^n$ and the Weil line carry different characters", fontsize=8)
    save(fig, "fig_eigen")


def fig_graph():
    """The closure graph of statements, drawn in three dimensions: the
    rule set of Section III (the same list is checked in lean/HodgeClosure.lean).
    A joint arrow from two statements means that both are needed."""
    fig = plt.figure(figsize=(3.4, 3.2))
    ax = fig.add_subplot(111, projection="3d")
    P = {"HC": (0, 0, 2.0), "F3": (0, -1.5, 1.6), "F2": (-1.3, 0.5, 1.0),
         "F3'": (1.3, 0.5, 1.0), "AB": (-1.3, 1.6, 0.4), "M": (0.0, 1.6, -0.2),
         "L": (-1.5, -0.9, 0.0), "V": (1.5, -0.9, 0.0)}
    single = [("F3", "HC"), ("HC", "F3"), ("HC", "F2"), ("HC", "F3'"),
              ("HC", "M"), ("F2", "AB"), ("AB", "F2"), ("L", "AB"), ("V", "AB")]
    joint = [(("AB", "F3'"), "HC"), (("L", "M"), "HC")]
    for a, b in single:
        pa, pb = np.array(P[a]), np.array(P[b])
        ax.quiver(*pa, *(pb - pa), arrow_length_ratio=0.12, color="#444444",
                  lw=0.8)
    for (a, b), c in joint:
        pa, pb, pc = np.array(P[a]), np.array(P[b]), np.array(P[c])
        m = (pa + pb) / 2
        ax.plot([pa[0], m[0]], [pa[1], m[1]], [pa[2], m[2]], color="#7a1f1f", lw=1.0)
        ax.plot([pb[0], m[0]], [pb[1], m[1]], [pb[2], m[2]], color="#7a1f1f", lw=1.0)
        ax.quiver(*m, *(pc - m), arrow_length_ratio=0.15, color="#7a1f1f", lw=1.0)
    for name, p in P.items():
        ax.scatter(*p, s=170, color="#f2c0bd" if name in ("F2", "F3'")
                   else "#dfe7f2", edgecolor="black", zorder=5)
        ax.text(p[0], p[1], p[2] + 0.2, name, ha="center", fontsize=8)
    ax.set_axis_off()
    ax.view_init(elev=18, azim=-50)
    ax.set_title("The closure graph: HC $\\Leftrightarrow$ (F2) $\\wedge$ (F3$'$)",
                 fontsize=8)
    save(fig, "fig_graph")


def fig_chain():
    """The chain of Theorem A for Q(sqrt 6): X' with an order-3 symplectic
    automorphism, its quotient Y (Hodge isometric to a surface Y' with a
    Nikulin involution), and the quotient Z; the multipliers 3, 1, 2 compose
    to 6, the square of the real multiplication."""
    fig = plt.figure(figsize=(3.4, 2.9))
    ax = fig.add_subplot(111, projection="3d")
    def surf(cx, cy, cz, col, k):
        u = np.linspace(0, 2 * np.pi, 40); v = np.linspace(0, 2 * np.pi, 20)
        U, V = np.meshgrid(u, v)
        R, r = 0.55, 0.22 + 0.04 * k
        X = cx + (R + r * np.cos(V)) * np.cos(U)
        Y = cy + (R + r * np.cos(V)) * np.sin(U)
        Z = cz + r * np.sin(V) * (1 + 0.3 * np.cos(k * U))
        ax.plot_surface(X, Y, Z, color=col, alpha=0.85, linewidth=0)
    surf(0, 0, 2.0, "#9fb4d8", 3); surf(1.6, 0, 1.0, "#c9d9b3", 1)
    surf(3.2, 0, 0.0, "#f2c0bd", 2)
    ax.text(0, 0, 2.55, r"$X'$, $\sigma$ of order 3", ha="center", fontsize=7)
    ax.text(1.6, 0, 1.55, r"$Y\cong Y'$, $\iota$ Nikulin", ha="center", fontsize=7)
    ax.text(3.2, 0, 0.55, r"$Z$", ha="center", fontsize=7)
    ax.quiver(0.6, 0, 1.9, 0.5, 0, -0.65, arrow_length_ratio=0.2, color="black", lw=0.9)
    ax.quiver(2.2, 0, 0.9, 0.5, 0, -0.65, arrow_length_ratio=0.2, color="black", lw=0.9)
    ax.text(0.95, 0, 1.75, r"$\deg 3$", fontsize=7)
    ax.text(2.55, 0, 0.75, r"$\deg 2$", fontsize=7)
    ax.text(1.6, 0, -0.9, r"multiplier $3\cdot1\cdot2=6=e^{2}$", ha="center", fontsize=7)
    ax.set_axis_off(); ax.view_init(elev=20, azim=-80)
    ax.set_title(r"Theorem A for $e=\sqrt{6}$: a chain of two symplectic quotients",
                 fontsize=8)
    save(fig, "fig_chain")


def fig_hankel():
    """The lower bound r(gamma) = (4+rho) n^2 - 2n for dim Ext^2 of an object
    whose Chern character has the polarised shape, against n and the Hankel
    rank rho; the markers are the two product cases, n = 3 and n = 4 with
    rho = 3 (57 and 104), and the proved bounds 69 and 640 on E_0^6, E_0^8."""
    fig = plt.figure(figsize=(3.4, 3.0))
    ax = fig.add_subplot(111, projection="3d")
    for rho, col in [(1, "#dfe7f2"), (2, "#9fb4d8"), (3, "#c0504d")]:
        for n in range(2, 7):
            ax.bar3d(n - 0.3, rho - 0.3, 0, 0.6, 0.6, (4 + rho) * n * n - 2 * n,
                     color=col, alpha=0.9)
    ax.text(3, 3, 70, "57", fontsize=7, ha="center")
    ax.text(4, 3, 118, "104", fontsize=7, ha="center")
    ax.set_xlabel(r"$n$", labelpad=2); ax.set_ylabel(r"Hankel rank $\rho$", labelpad=2)
    ax.set_zlabel(r"$r(\gamma)$", labelpad=2)
    ax.set_xticks(range(2, 7)); ax.set_yticks([1, 2, 3])
    ax.tick_params(labelsize=7)
    ax.view_init(elev=24, azim=-58)
    ax.set_title(r"$r(\gamma)=(4+\rho)n^{2}-2n$: the rank the criterion demands",
                 fontsize=8)
    save(fig, "fig_hankel")


def fig_product():
    """The product locus inside the polarised Weil domain: the tangent space
    of the product locus has dimension m^2 + m'^2 and the n^2 - m^2 - m'^2
    mixed directions obstruct every exterior product; the object of Section
    VI has first-order Hodge locus the whole tangent space."""
    fig = plt.figure(figsize=(3.4, 3.0))
    ax = fig.add_subplot(111, projection="3d")
    u = np.linspace(-1.5, 1.5, 40); v = np.linspace(-1.5, 1.5, 40)
    U, V = np.meshgrid(u, v)
    ax.plot_surface(U, V, 0.15 * (U**2 + V**2), color="#dfe7f2", alpha=0.7,
                    linewidth=0)
    t = np.linspace(-1.4, 1.4, 60)
    ax.plot(t, 0 * t, 0.15 * t**2 + 0.01, color="#1f3f7a", lw=2.0)
    ax.scatter([0], [0], [0.02], s=40, color="black", marker="*")
    ax.quiver(0, 0, 0.02, 0.9, 0, 0, color="#1f3f7a", arrow_length_ratio=0.15, lw=1.2)
    ax.quiver(0, 0, 0.02, 0, 0.9, 0, color="#c0504d", arrow_length_ratio=0.15, lw=1.2)
    ax.text(0.95, 0, 0.1, r"$T$(product locus), $m^{2}+m'^{2}$", fontsize=6.5)
    ax.text(0, 0.95, 0.1, r"mixed directions, $n^{2}-m^{2}-m'^{2}$", fontsize=6.5,
            color="#c0504d")
    ax.text(0, 0, -0.35, r"$A\times A'$", fontsize=8, ha="center")
    ax.set_axis_off(); ax.view_init(elev=28, azim=-60)
    ax.set_title(r"$\mathcal{D}_{n,n}$ near a product point: 4 (resp. 8) mixed"
                 "\n" r"directions obstruct every $F\boxtimes G'$", fontsize=8)
    save(fig, "fig_product")


def fig_link():
    """The sixfold link: the Mumford fourfold X (twice) and the abelian
    sixfold Z_K over the same Shimura curve, and the Hodge class xi in
    H^1(X) x H^1(X) x H^2(Z_K) that identifies the two copies of T."""
    fig = plt.figure(figsize=(3.4, 3.0))
    ax = fig.add_subplot(111, projection="3d")
    s = np.linspace(-1.5, 1.5, 100)
    ax.plot(s, 0.3 * np.sin(2 * s), 0 * s, color="black", lw=1.2)
    ax.text(1.6, 0.3 * np.sin(3.0), 0, r"$C$", fontsize=8)
    def fibre(x0, z0, col, lab):
        th = np.linspace(0, 2 * np.pi, 60)
        ax.plot(x0 + 0 * th, 0.3 * np.sin(2 * x0) + 0.35 * np.cos(th),
                z0 + 0.35 * np.sin(th), color=col, lw=1.6)
        ax.text(x0, 0.3 * np.sin(2 * x0) + 0.5, z0 + 0.45, lab, fontsize=7,
                ha="center")
    fibre(-0.9, 1.2, "#1f3f7a", r"$X_t$"); fibre(0.0, 1.2, "#1f3f7a", r"$X_t$")
    fibre(0.9, 1.2, "#7a1f1f", r"$Z_{K,t}$")
    for x0 in (-0.9, 0.0, 0.9):
        ax.plot([x0, x0], [0.3 * np.sin(2 * x0)] * 2, [0, 0.85], color="grey", lw=0.6)
    ax.plot([-0.9, 0.0, 0.9], [0.3 * np.sin(-1.8) - 0.35, 0.3 * np.sin(0) - 0.35,
            0.3 * np.sin(1.8) - 0.35], [1.2, 1.2, 1.2], color="#2e7d32", lw=1.4)
    ax.text(0.0, -0.75, 1.35, r"$\xi_t\in H^{1}(X)\otimes H^{1}(X)\otimes H^{2}(Z_K)$",
            fontsize=6.5, ha="center", color="#2e7d32")
    ax.text(0.0, 0.0, 2.0, r"$T_X(-1);\longrightarrow;T_Z\quad(\xi=m_e\circ\iota)$", fontsize=7, ha="center")
    ax.set_axis_off(); ax.view_init(elev=22, azim=-70)
    ax.set_title("The sixfold link over the Shimura curve", fontsize=8)
    save(fig, "fig_link")


def fig_fricke():
    """The Fricke families of Theorem V.8: over the modular curve X_0(N) with
    Fricke coordinate t, the involution w(t) = N^k/t exchanges the cusps 0 and
    infinity and the two elliptic points e_1, e_2; the twist X_p at the pair
    {p, N^k/p} is carried to itself by the fibrewise isogeny f of degree N,
    and f^* is the real multiplication by sqrt N on the transcendental
    lattice of rank 6."""
    fig = plt.figure(figsize=(3.4, 3.1))
    ax = fig.add_subplot(111, projection="3d")
    # the base P^1_t as a line, with the special points
    ts = np.linspace(-0.2, 4.2, 50)
    ax.plot(ts, 0 * ts, 0 * ts, color="black", lw=1.0)
    pts = {0.0: r"$0$", 4.0: r"$\infty$", 1.2: r"$e_1$", 2.8: r"$e_2$",
           0.6: r"$p$", 3.4: r"$N^{k}/p$"}
    for x, lab in pts.items():
        ax.scatter([x], [0], [0], color="black", s=10)
        ax.text(x, -0.35, -0.25, lab, fontsize=7, ha="center")
    # the Fricke involution as arcs under the base
    def arc(x0, x1, depth, col):
        u = np.linspace(0, np.pi, 40)
        ax.plot((x0 + x1) / 2 + (x1 - x0) / 2 * np.cos(u), 0 * u, -depth * np.sin(u), color=col, lw=0.8, ls="--")
    arc(0.0, 4.0, 1.1, "#555555"); arc(1.2, 2.8, 0.6, "#555555"); arc(0.6, 3.4, 0.85, "#b03a2e")
    ax.text(2.0, 0, -1.35, r"$w(t)=N^{k}/t$", fontsize=7, ha="center", color="#555555")
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
    ax.text(0.6, 0, 2.35, r"$\mathrm{I}_0^{*}$", fontsize=7, ha="center")
    ax.text(3.4, 0, 2.35, r"$\mathrm{I}_0^{*}$", fontsize=7, ha="center")
    ax.text(2.0, 0, 2.25, r"$X_p=X_{p,N^{k}/p}$", fontsize=7, ha="center")
    # the self-isogeny
    u = np.linspace(0, np.pi, 40)
    ax.plot(2.0 + 1.6 * np.cos(u), 0 * u, 2.6 + 0.5 * np.sin(u), color="#b03a2e", lw=1.0)
    ax.quiver(3.55, 0, 2.65, 0.05, 0, -0.1, arrow_length_ratio=0.9, color="#b03a2e", lw=1.0)
    ax.text(2.0, 0, 3.3, r"$f$, degree $N$: $f^{*}=\pm\sqrt{N}$ on $T(X_p)$, rank $6$", fontsize=7, ha="center", color="#b03a2e")
    ax.set_xlim(-0.3, 4.3); ax.set_ylim(-1.2, 1.2); ax.set_zlim(-1.5, 3.4)
    ax.set_axis_off(); ax.view_init(elev=16, azim=-85)
    ax.set_title(r"The family $\mathfrak{A}_N$, $N\in\{5,7\}$: twists at a pair exchanged by $w$",
                 fontsize=8)
    save(fig, "fig_fricke")


if __name__ == "__main__":
    fig_locus(); fig_eigen(); fig_graph(); fig_chain()
    fig_hankel(); fig_product(); fig_link(); fig_fricke()
    print("figures written to", os.path.abspath(OUT))
