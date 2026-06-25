# mathlib-audit.md — Mathlib coverage of the JL analytic prerequisites

Living document. Mathlib pinned at **v4.31.0** (toolchain `leanprover/lean4:v4.31.0`).
All paths below are under `.lake/packages/mathlib/Mathlib/`.
Classification: **OFF-THE-SHELF** (use directly) / **DERIVABLE** (compose existing API) /
**MISSING** (must build infrastructure, or `sorry`).

---

## Verdict (TL;DR)

| Prerequisite | Status | Where |
|---|---|---|
| Sub-Gaussian MGF framework | **OFF-THE-SHELF** | `Probability/Moments/SubGaussian.lean` |
| Hoeffding's lemma (bounded ⇒ sub-Gaussian) | **OFF-THE-SHELF** | `SubGaussian.lean:839` |
| Hoeffding's inequality (sum tail) | **OFF-THE-SHELF** | `SubGaussian.lean:780` |
| Chernoff bound (sub-Gaussian tail) | **OFF-THE-SHELF** | `SubGaussian.lean:334` |
| MGF/CGF, tilted measures, integrable-exp | **OFF-THE-SHELF** | `Probability/Moments/*` |
| Independence (`iIndepFun`), variance, covariance | **OFF-THE-SHELF** | `Probability/Independence`, `Moments/Variance.lean` |
| Gaussian (real + multivariate, char. fun.) | **OFF-THE-SHELF** | `Probability/Distributions/Gaussian/` |
| Binomial / Chernoff count of "bad" coords (Case 2) | **DERIVABLE** | `Distributions/Binomial.lean` + sub-Gaussian |
| Sub-exponential / sub-gamma RV class + Bernstein | **MISSING** | — (analytic "subexp growth" is unrelated) |
| Chi-squared distribution + tail bounds | **MISSING** (Gamma exists, no χ², no tails) | `Distributions/Gamma.lean` only |
| **Berry–Esseen theorem (quantitative CLT)** | **MISSING** | — (only *qualitative* CLT exists) |
| Existing JL / random-projection formalization | **MISSING** | — (no hits) |

**Go/no-go:** GO. The norm-preservation half (N1), the structural extension (N3), and Case 1/2
of the mod-q half are "weeks of bookkeeping over existing infra." The single make-or-break gap is
**Berry–Esseen** (Case 3 / Conjecture 1) — confirmed absent. That is exactly the irreducible
human-hard core the mission predicted; isolating it behind one annotated `sorry` is the win.

**Two proof architectures (added after reading LNP22 — see paper-to-lean-map.md §2b/§4):** the mod-q
soundness has *two* literature routes with *different* irreducible gaps.
1. **RoKoko/BS23** (the headline target; modulus threshold `b` is **m-independent**, `q/125`):
   gap = **Berry–Esseen** anti-concentration (Case 3). Unavoidable for the m-independent bound.
2. **LNP22** (modulus threshold `b` is **m-dependent**, `P/41m`): gap = **discrete→Gaussian χ²
   substitution** only. The mask-vector handling is a fully-rigorous **symmetrization trick**
   (Bin₁−Bin₁=Bin₂ + triangle inequality), and the ℓ∞ range proof (Lemma 2.7) is a proven leaf.
   This route is **Berry–Esseen-free** and far more Lean-tractable, but proves a weaker (m-dependent)
   lemma than RoKoko needs.
**Implication for scope:** Berry–Esseen stays the target gap for RoKoko Conjecture 1, but LNP22
supplies cheap fully-rigorous wins (symmetrization, ℓ∞ ARP, the Chernoff case) and relocates the
*other* route's gap onto **χ² tail bounds**, which Mathlib can support far better than Berry–Esseen
(see §3c — `Gamma` exists, χ² tails derivable). A rigorously-closed *variant* of the lemma is
therefore reachable via the Gaussian model, even though the discrete headline result is not.

---

## 1. OFF-THE-SHELF — sub-Gaussian & concentration

`Probability/Moments/SubGaussian.lean` is a full sub-Gaussian MGF library:

- `ProbabilityTheory.HasSubgaussianMGF (X) (c) (μ)` — `mgf X μ t ≤ exp (c·t²/2)` + integrability.
  Also a kernel/conditional version `Kernel.HasSubgaussianMGF`, `HasCondSubgaussianMGF`.
- `HasSubgaussianMGF.measure_ge_le` (`:334`) — **Chernoff right-tail**:
  `μ.real {ω | ε ≤ X ω} ≤ exp(-ε²/(2c))`.
- `HasSubgaussianMGF.add` (`:407`) — sum of independent sub-Gaussians is sub-Gaussian (`c` adds).
- `measure_sum_ge_le_of_iIndepFun` (`:780`) — **Hoeffding's inequality**:
  `μ.real {ω | ε ≤ ∑ i∈s, X i ω} ≤ exp(-ε²/(2·∑ c i))` for independent sub-Gaussian `X i`.
  Range variant `measure_sum_range_ge_le_of_iIndepFun` (`:787`).
- `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` (`:839`) — **Hoeffding's lemma**: zero-mean
  `X ∈ [a,b]` a.s. ⇒ sub-Gaussian with `c = ((b-a)/2)²`. Corollary `hasSubgaussianMGF_of_mem_Icc`
  (`:859`) centers an arbitrary bounded `X`.
- `measure_sum_ge_le_of_HasCondSubgaussianMGF` — Azuma–Hoeffding (martingale version).

**Consequences for us:**
- **N0 is free.** χ has support `{−1,0,1} ⊂ [−1,1]`, mean 0 ⇒ sub-Gaussian directly.
  A row `⟨r,w⟩ = Σ rᵢwᵢ` is a sum of independent zero-mean `rᵢwᵢ ∈ [−|wᵢ|,|wᵢ|]` ⇒ sub-Gaussian.
- **N1 upper tail is reachable now** with LOOSE constants: `‖Jw‖² = Σ_j ⟨rⱼ,w⟩²`, each term is a
  bounded nonneg. RV (in `[0,‖w‖₁²]`), so its centering is sub-Gaussian; Hoeffding-for-sums bounds
  the upper deviation. Tightness `[√30,√337]` does NOT follow — see §3.
- **Two-sidedness caveat:** the API gives one-sided right tails. The lower tail of `‖Jw‖²` (the
  `α_rp` endpoint / small-ball) = right tail of `−‖Jw‖²`; `−⟨r,w⟩²` is bounded ⇒ also sub-Gaussian,
  so the lower tail is reachable too (loose constant). No two-sided/`|·|` lemma is pre-packaged;
  apply to `X` and `−X` and union-bound.

## 2. OFF-THE-SHELF — supporting infrastructure
- **Independence:** `Probability/Independence/Basic.lean` — `iIndepFun`, needed to model i.i.d. J.
- **Moments:** `Probability/Moments/{Basic,MGFAnalytic,IntegrableExpMul,Tilted,Variance,
  Covariance,ComplexMGF}.lean`. `Variance.lean` for `E[⟨r,w⟩²]=½‖w‖²` bookkeeping.
- **Gaussian:** `Probability/Distributions/Gaussian/{Basic,Real,Multivariate,CharFun,Fernique}.lean`,
  `HasGaussianLaw`, `gaussianReal`. Enables the *Gaussian-model* route (treat χ as Gaussian) —
  but the χ² tail bounds you'd need on top are absent (§3).
- **Linear algebra / norms:** `EuclideanSpace`, `Matrix`, `Matrix.kronecker` (`I ⊗ J` for N3),
  `ZMod q` / `Int.emod` (the `mod q` reduction). All standard, present, off-the-shelf.

## 3. MISSING — the gaps that decide scope

### 3a. Berry–Esseen theorem — **MISSING. This is the make-or-break gap.**
- `Probability/CentralLimitTheorem.lean` exists but is **qualitative only**:
  `tendstoInDistribution_inv_sqrt_mul_sum` gives `TendstoInDistribution → 𝓝(gaussian)`, i.e.
  convergence in distribution via characteristic functions (`Gaussian/CharFun.lean`,
  `Analysis/Fourier/...`). **No convergence rate. No `sup|F_n − Φ| ≤ C·ρ/(σ³√n)` bound.**
- Searches for `berry`, `esseen`, `lindeberg`, quantitative CLT: **zero hits** in all packages.
- **Impact:** BS23 Lemma 4.2 **Case 3** and RoKoko **Conjecture 1** both rest on Berry–Esseen to
  show a row is "bad" with probability `p = 0.39 + 2·0.15 < 1` (constant). The qualitative CLT
  cannot deliver an *explicit finite-n* probability bound, so this step is unreachable from
  Mathlib as-is. Options:
  1. **Localize (recommended):** state the Berry–Esseen inequality as an explicit hypothesis /
     axiom-shaped lemma with one annotated `sorry`; prove everything else around it.
  2. **Build it:** formalize Berry–Esseen from scratch (smoothing inequality + char.-function
     bounds). Large independent project (the classical proof is several hundred lines of hard
     analysis); out of scope for this phase.

### 3b. Sub-exponential / sub-gamma class + Bernstein inequality — **MISSING.**
- No `SubExponential`/`SubGamma` RV class; the only `subexponential` hits are the unrelated
  complex-analysis "subexponential growth rate" (`Analysis/SpecialFunctions/CompareExp.lean`).
- **Impact:** the *tight* N1 window `[√30,√337]` (and the matching `Θ(√log)` in Conjecture 1's
  norm-preservation half) is most naturally a Bernstein bound on the sub-exponential `⟨rⱼ,w⟩²`.
  Mathlib's sub-Gaussian-for-sums gives the right *shape* with loose constants. To get tight
  constants either (a) build a small sub-exponential/Bernstein layer, or (b) use the Gaussian/χ²
  route. **Derivable with effort**, not a hard blocker for *localization* (only for tight concrete
  constants).

### 3c. Chi-squared distribution + tail bounds — **MISSING, but the most tractable gap.**
- `Distributions/Gamma.lean` exists; **no `chiSquared`**, and no Gamma/χ² tail (deviation) lemmas.
- **Impact:** the clean "rigorous Gaussian analog" (RoKoko App A; LNP22 **Lemma 2.8** makes it
  explicit: `‖Rw‖² = ½‖w‖²·χ²[256]`, bounds = `Pr[χ²<26]`, `Pr[χ²>674]`) needs χ² concentration
  Mathlib lacks. **But χ² = Gamma(n/2, 2)**, so this is derivable from the existing `Gamma`
  distribution + MGF/Chernoff (which Mathlib HAS, §1) — no Berry–Esseen needed. Of the two
  architecture gaps (§3a Berry–Esseen vs this), **this is the one Mathlib can actually support.**
- For the LNP22 route, this χ² tail (for a *Gaussian* R) is the ENTIRE remaining gap once the
  rigorous symmetrization (Lemma 2.9→2.10) and Chernoff case are in place. The residual
  discrete-Bin₁→Gaussian step is the only genuinely heuristic nub there.

### 3d. Existing JL formalization — **MISSING (as expected).**
- No `johnson`/`lindenstrauss`/`random_projection` results. We are building this fresh; nothing to
  reuse or conflict with.

---

## 4. Recommended proof path (feeds task 4 go/no-go)

**Reachable now (over existing infra), fully rigorous:**
- N0 (per-row sub-Gaussianity) — `hasSubgaussianMGF_of_mem_Icc...`.
- N3 (Lemma 6, I⊗J extension) — structural, union bound; depends only on N1/N2 *statements*.
  → **Start here** (mission task 6): cheapest real proof, de-risks the skeleton.
- **L7 (LNP22 Lemma 2.7, ℓ∞ ARP)** — elementary per-row argument; a proven, self-contained leaf.
- **L9a (symmetrization) + L10 Case `‖w‖∞≥P/4m`** — Bin₁−Bin₁=Bin₂, triangle inequality, Chernoff
  `(1/2)^256`. Reduces the masked mod-q soundness to the *norm bound* with no anti-concentration.
- N2 Case 1 — reduces to N1.  N2 Case 2 / L10 Chernoff case — binomial tail (Mathlib + `Binomial`).
- N1 (Lemma 5 norm preservation) — both tails via Hoeffding-for-sums, **loose** constants.

**Needs infrastructure first (defer / build / `sorry`):**
- Tight N1 window `[√30,√337]` → sub-exponential Bernstein (§3b) or χ² tails (§3c).
- **χ² tail bound (§3c)** — the LNP22-route gap (L8) and the rigorous Gaussian-model norm window.
  **Derivable from Mathlib `Gamma` + MGF/Chernoff** — the recommended infrastructure to build.
- N2 Case 3 → **Berry–Esseen (§3a)** — the one irreducible human-hard core for the m-INDEPENDENT `b`.
- N4 Conjecture 1 → same Berry–Esseen + constant-`p(α,β)<1`, plus χ²/Bernstein scaling.

**The irreducible human-hard core** (for RoKoko's headline m-independent result): the Berry–Esseen
anti-concentration constant `p = p(α,β) < 1` of Case 3, reused unchanged in Conjecture 1. Building
Berry–Esseen in Lean is a separate large project; **localization is the recommended scope.**
**Recommended sequencing:** (1) N3 + L7 + L9a + L10-Chernoff (cheap, fully rigorous); (2) build
χ²-tails from `Gamma` and close the *Gaussian-model* norm bound (L8/N1) rigorously; (3) localize
the discrete headline result behind the single Berry–Esseen `sorry`.
