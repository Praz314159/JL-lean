"""
THE HERO, in 3D.  Distribution of <r,w> mod q as a density curtain on the circle Z/qZ.

The circle lives in the (x1,x2)=(cos,sin) plane; the height above each point is the probability
density.  Over random r the density is a single near-Gaussian bump (Berry-Esseen), spread
sigma ~ q/15.  The verifier accepts iff the value lands in the bad arc |x|<=c (red sector).
The bump is wider than the arc, so <=~40% of the curtain's mass sits over it; the antipodal wrap
region (gray) is ~7 sigma away with negligible mass.
"""
import numpy as np
import matplotlib.pyplot as plt
from matplotlib import cm

plt.rcParams.update({"font.size": 12, "figure.dpi": 150})

sig_t = 2*np.pi*(1/(11*np.sqrt(2)))      # angular spread (q = 1)
c_t   = 2*np.pi*(1/30.)                   # bad-arc half-angle
from scipy.stats import norm
p0 = 2*norm.cdf((1/30.)/(1/(11*np.sqrt(2)))) - 1

N, M = 720, 48
theta = np.linspace(-np.pi, np.pi, N)
def g(th): return sum(np.exp(-((th + 2*np.pi*k)**2)/(2*sig_t**2)) for k in (-1, 0, 1))
H = g(theta); H = 1.30*H/H.max()
tt = np.linspace(0, 1, M)
TH, TT = np.meshgrid(theta, tt)
X, Y, Z = np.cos(TH), np.sin(TH), TT*H[None, :]

bad  = np.abs(theta) <= c_t
wrap = np.abs(np.abs(theta) - np.pi) <= c_t

# colour by ABSOLUTE height (tails stay pale, only the peak saturates -> dimensional look)
zmax = H.max()
frac = (TT * H[None, :]) / zmax                  # (M, N) in [0,1]
shade = 0.18 + 0.78 * frac
RB, BL = cm.Reds(shade), cm.Blues(shade)         # (M, N, 4) each
FC = np.where(bad[None, :, None], RB, BL)

fig = plt.figure(figsize=(10.5, 8.6))
ax = fig.add_subplot(111, projection="3d")
surf = ax.plot_surface(X, Y, Z, facecolors=FC, rstride=1, cstride=1, linewidth=0,
                       antialiased=True, shade=False, zorder=2)
surf.set_rasterized(True)
# crisp outlines: density profile (top) + base circle
ax.plot(np.cos(theta), np.sin(theta), H, color="k", lw=1.6, zorder=4)
ax.plot(np.cos(theta), np.sin(theta), 0*theta, color="k", lw=1.4, zorder=1)
# bad arc + wrap region on the base
ax.plot(np.cos(theta[bad]),  np.sin(theta[bad]),  0*theta[bad],  color="#c0392b", lw=6, zorder=5)
ax.plot(np.cos(theta[wrap]), np.sin(theta[wrap]), 0*theta[wrap], color="#8a8f96", lw=6, zorder=3)

# clean look -- bump (theta=0 -> (1,0)) brought to front-centre
ax.view_init(elev=22, azim=-118)
ax.set_box_aspect((1, 1, 0.62))
ax.set_zlim(0, 1.45); ax.set_xlim(-1.15, 1.15); ax.set_ylim(-1.15, 1.15)
for pane in (ax.xaxis, ax.yaxis, ax.zaxis):
    pane.pane.set_facecolor((1, 1, 1, 0)); pane.pane.set_edgecolor((1, 1, 1, 0))
ax.grid(False)
ax.set_xticks([-1, 0, 1]); ax.set_yticks([-1, 0, 1]); ax.set_zticks([])
ax.set_xlabel(r"$x_1=\cos(2\pi x/q)$", labelpad=6)
ax.set_ylabel(r"$x_2=\sin(2\pi x/q)$", labelpad=6)

# annotations (2D overlay in figure coords -> clean leader-free callouts)
ax.text2D(0.50, 0.965, "Case 3: the distribution of  $\\langle r,w\\rangle \\,\\mathrm{mod}\\,q$  on the circle  $\\mathbb{Z}/q\\mathbb{Z}$",
          transform=ax.transAxes, ha="center", fontsize=15, fontweight="bold")
# legend (proxy patches) -- replaces scattered callouts
from matplotlib.patches import Patch
handles = [
    Patch(facecolor=cm.Blues(0.72), edgecolor="k", lw=0.6,
          label="near-Gaussian bump (Berry–Esseen),  $\\sigma\\approx q/15$"),
    Patch(facecolor=cm.Reds(0.72), edgecolor="k", lw=0.6,
          label=f"bad arc  $|x|\\leq c$:  $\\approx{p0*100:.0f}\\%$ of the mass (worst case)"),
    Patch(facecolor="#8a8f96", edgecolor="k", lw=0.6,
          label="wrap region:  $\\approx 7\\sigma$ away, negligible mass"),
]
ax.legend(handles=handles, loc="upper left", bbox_to_anchor=(-0.02, 0.90),
          fontsize=9, frameon=True, framealpha=0.95, borderpad=0.5, labelspacing=0.4,
          handlelength=1.1, handletextpad=0.5, edgecolor="#cccccc")

out = "/private/tmp/claude-501/-Users-prashanth-Desktop-Research-cryptography-JL-lean/85108a5f-92f8-4859-95d4-6aa61d83cd29/scratchpad/jl_circle3d.png"
fig.savefig(out, bbox_inches="tight", dpi=150)
print("wrote", out, f"| p0={p0:.3f} sig_theta={np.degrees(sig_t):.0f}deg badarc=+-{np.degrees(c_t):.0f}deg")
