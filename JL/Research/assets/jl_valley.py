"""THE CRUX: per-row failure p(sigma) is a valley in the sub-witness spread sigma."""
import numpy as np
import matplotlib.pyplot as plt
from scipy.stats import norm

plt.rcParams.update({"font.size": 12, "axes.titlesize": 14, "axes.linewidth": 0.8,
                     "figure.dpi": 140})
C0, c, winf = 0.56, 1/30., 1/60.                  # q = 1
s   = np.linspace(0.045, 0.55, 800)               # s = ||v||_2 / q
sig = s/np.sqrt(2)
p0  = 2*norm.cdf(c/sig) - 1
d2  = 2*C0*winf/sig
tau = 2*np.exp(-((0.5 - c)**2)/(2*sig**2))
tot = p0 + d2 + tau
BLU, ORA, GRY, RED, GRN = "#2e6da4", "#e08214", "#9aa0a6", "#c0392b", "#2c8a4a"

fig, ax = plt.subplots(figsize=(11, 6.3))
ax.plot(s, tot, color="k",  lw=3.0, zorder=5, label="total  $p=p_0+2\\delta+\\tau$")
ax.plot(s, p0,  color=BLU,  lw=1.8, ls=(0,(5,2)), label="$p_0$  bad-arc mass")
ax.plot(s, d2,  color=ORA,  lw=1.8, ls=(0,(5,2)), label="$2\\delta$  Berry–Esseen slack")
ax.plot(s, tau, color=GRY,  lw=1.8, ls=(0,(5,2)), label="$\\tau$  wrap tail")
ax.axhline(1.0, color=RED, lw=1.5, ls=":", label="ceiling  $p=1$")

# sub-witness window + valley floor
ax.axvspan(1/11, 1/10, color=RED, alpha=0.12, lw=0,
           label="sub-witness window  $[q/11,q/10)$")
i = np.argmin(tot)
ax.plot([s[i]], [tot[i]], "o", color=GRN, ms=8, zorder=6,
        label=f"valley floor: min $p\\approx{tot[i]:.2f}$  (margin $1{{-}}p\\approx{1-tot[i]:.2f}$)")

ax.set_xlim(0.045, 0.55); ax.set_ylim(0, 1.30)
ax.set_xlabel(r"sub-witness size  $\|v\|_2 / q$")
ax.set_ylabel("per-row failure probability  $p$")
ax.set_title(r"Per-row failure  $p=p_0+2\delta+\tau$  vs. sub-witness size")
for sp in ("top", "right"): ax.spines[sp].set_visible(False)

# compact legend in the bottom-right, just above the blue p0 tail
ax.legend(loc="lower right", bbox_to_anchor=(0.99, 0.17), fontsize=7.5, frameon=True,
          framealpha=0.95, edgecolor="#cccccc", borderpad=0.4, labelspacing=0.28,
          handlelength=1.3, handletextpad=0.4)

fig.tight_layout()
out = "/private/tmp/claude-501/-Users-prashanth-Desktop-Research-cryptography-JL-lean/85108a5f-92f8-4859-95d4-6aa61d83cd29/scratchpad/jl_valley.png"
fig.savefig(out, bbox_inches="tight")
print("wrote", out, f"| floor p={tot[i]:.3f} @ s={s[i]:.3f} | window-left p={tot[np.argmin(np.abs(s-1/11))]:.3f}")
