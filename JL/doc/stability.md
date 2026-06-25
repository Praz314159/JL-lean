# JL-lean — Stability Tiers

What downstream consumers should expect from each part of the tree. The library is at its
*foundation* stage: the model and the statement DAG are laid down (0 `sorry`, 0 `axiom`,
CI-enforced), and proving is just beginning. See [`paper-to-lean-map.md`](paper-to-lean-map.md) for
the full DAG and [`mathlib-audit.md`](mathlib-audit.md) for Mathlib coverage.

## Stable (safe to depend on)

- **Probability model & geometry** ([`JL/Defs.lean`](../Defs.lean)): `IsChiEntry`, `IsChiMatrix`,
  `IsBin2Matrix`, `l2Norm`, `sqNorm`, `proj`, `normRatio`, `projModL2Norm`, `centeredMod`,
  `normInf`, `maskedProjModL2Norm` (bounds on `l2Norm`; squared internally via `l2Norm_sq`). These
  definitions are the public interface; signatures may still be refined (e.g. a future `JLSource`
  typeclass — see below) but the intended meaning is fixed.

## Proved (theorems, machine-checked)

- **ℓ₂/squared bridge** ([`JL/Defs.lean`](../Defs.lean)): `sqNorm_nonneg`, `l2Norm_nonneg`,
  `l2Norm_sq : l2Norm v ^ 2 = sqNorm v`.
- **N3 `lemma6_structured`** ([`JL/RoKoko.lean`](../RoKoko.lean)) — the Lemma 6 union bound: from the
  per-block norm-window hypothesis, the probability that *some* `(column, block)` pair violates the
  window is `≤ κ·r·blocks`. (The Pythagorean per-column concatenation, combining blocks into one
  column window, is still deferred to the full matrix version.)
- **N0 `n0_rowSubgaussian`** ([`JL/RoKoko.lean`](../RoKoko.lean)) — each row inner product `⟨rᵢ,w⟩` is
  sub-Gaussian with parameter `‖w‖₂²`: reindex the entry independence to row `i`, scale by the
  witness coordinates (`iIndepFun.precomp`/`.comp`), apply Hoeffding's lemma per coordinate
  (`hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`), and sum (`HasSubgaussianMGF.sum_of_iIndepFun`).
- **N1 `lemma5_norm_preservation`** ([`JL/RoKoko.lean`](../RoKoko.lean)) — Pillar 1, RoKoko Lemma 5 (I).
  Proved **conditional on `SqNormConcentrationHyp`** (the GHL21 concentration, deferred derivable
  input): the norm window `[√a, √b]` is the `√·` image of the squared window `[a, b]`, via
  `normRatio_eq_sqrt` + `l2Norm_sq`. The `√·`/window/division bookkeeping is fully proved; only the
  analytic concentration is assumed. Also: bridge lemmas `sqNorm_pos`, `normRatio_eq_sqrt`.
- **N2 assembly `lemma5_modq_soundness`** ([`JL/RoKoko.lean`](../RoKoko.lean)) — Lemma 5 (II) mod-q
  soundness, **conditional on `Case1Hyp`/`Case2Hyp`/`Case3Hyp`**. The proved content is BS23
  Appendix A's *case split*: the three geometric regimes (`‖w‖₂<q/10` / `‖w‖∞≥q/60` /
  `‖w‖₂≥q/10 ∧ ‖w‖∞<q/60`) are exhaustive, and since `w` is fixed the bad-event bound dispatches to
  the one applicable case (no union over regimes). Each `CaseᵢHyp` is the same body restricted to its
  regime; discharge paths: Case 1 → N1 + a no-wrap bound; Case 2 → Chernoff; Case 3 → `BerryEsseenHyp`
  + the `v`-construction (the irreducible core).

## Assumed analytic inputs (named hypotheses — NOT proved here)

These are the localized gaps. Anything depending on them carries the hypothesis explicitly.

- **`JL.Analytic.BerryEsseenHyp`** ([`JL/Analytic/BerryEsseen.lean`](../Analytic/BerryEsseen.lean)) —
  the Lyapunov-form quantitative CLT. Absent from Mathlib (only a *qualitative* CLT exists). This is
  **THE irreducible gap** for the RoKoko/BS23 route (N2 Case 3, Conjecture 1). Stability: **assumed**.
- **`JL.Analytic.ChiSquaredTailHyp`** ([`JL/Analytic/ChiSquared.lean`](../Analytic/ChiSquared.lean)) —
  χ²_n tail bounds. **Derivable** from Mathlib's `Gamma` distribution + MGF/Chernoff (χ² = Gamma(n/2,2));
  assumed for now, expected to be discharged in-tree. Stability: **assumed (derivable)**.
- **`JL.Analytic.SqNormConcentrationHyp`** ([`JL/Analytic/SubExponential.lean`](../Analytic/SubExponential.lean)) —
  the **GHL21 concentration bound** for `‖Jw‖₂²/‖w‖₂²` (squared-ratio form), i.e. sub-exponential
  Bernstein applied to `∑ⱼ⟨rⱼ,w⟩²`. **Derivable** but Mathlib lacks the sub-exponential layer.
  Stability: **assumed (derivable)**. *Discharge targets (come back to these):* (a) the χ²/Gaussian
  route via `ChiSquaredTailHyp` (= GHL21's own argument, made rigorous; Mathlib-`Gamma`-derivable);
  (b) the discrete sub-exponential Bernstein layer (Achlioptas-rigorous; build from scratch).

## Target statements (to be proved; currently `…_Statement : Prop` defs)

Do not depend on these as if proved — they are formal targets, not theorems, until a `theorem`
discharging them appears and this file is updated.

- **N2 cases** ([`JL/RoKoko.lean`](../RoKoko.lean)) — `Case1Hyp` (→ N1 + no-wrap), `Case2Hyp`
  (Chernoff), `Case3Hyp` (→ `BerryEsseenHyp` + `v`-construction). The N2 *assembly* is now
  **Proved**-conditional (above); these per-case bounds are the remaining targets. Discharging
  `Case1Hyp` (from N1) is the cheapest next step; `Case3Hyp` is the irreducible core.
- **Discharge `JLScalingHyp`** — the remaining substance behind Conjecture 1: build quantitative
  (rate-carrying) versions of N1 (Pillar 1, via Bernstein) and N2 (Pillar 2, via `BerryEsseenHyp` +
  uniform `p(α,β)<1`) to *construct* a working schedule. This is the genuinely conjectural core.
- **L7, L9, L9a, L10** ([`JL/LNP.lean`](../LNP.lean)) — the LNP22 Berry–Esseen-free route. L7 (ℓ∞ ARP)
  and L9a (symmetrization) are fully rigorous; L10/L9 bottom out at `ChiSquaredTailHyp`, not
  Berry–Esseen.

## Research / conjectured

- **Conjecture 1** ([`JL/Research/Conjecture.lean`](../Research/Conjecture.lean)) — asymptotic
  `Θ(√log(1/κ))` scaling, tagged `JLRegime.conjectured`. Stability: **research / conjectured**.
  Built in CI, not in `import JL`.
  - **`Conjecture1_Statement` is now non-vacuous**: it asserts a parameter *schedule* that *achieves*
    the JL guarantee (`AchievesJL` = Lemma 5 (I)+(II) bodies) at each `κ`, AND has the `Θ`
    asymptotics. (The original skeleton form — "functions with these growth rates exist" — was
    trivially true; the content is coupling the rates to the guarantee.)
  - **`conjecture1_of_jlScaling` (PROVEN reduction)**: `JLScalingHyp q → Conjecture1_Statement q`.
    Proved content = the Landau packaging (pointwise `∀κ∈(0,1)` rate bounds ↦ `Θ` as `κ→0⁺`, via
    `eventually_of_mem` on `Ioo 0 1 ∈ 𝓝[>] 0`). `JLScalingHyp` (a schedule achieving the guarantee
    with explicit rates) is the sharp residual; discharging it reduces to N1 + Bernstein (Pillar 1)
    and N2 with `BerryEsseenHyp` + the uniform `p(α,β)<1` claim (Pillar 2 / Case 3 — the open nub).

## Out of scope (for now)

- A `JLSource` typeclass unifying χ / Bin₂ / Gaussian. Deliberately deferred — current code uses
  concrete per-distribution predicates (`IsChiEntry`, `IsBin2Matrix`) for speed; a typeclass refactor
  is a clean follow-up once the proofs settle.
- Building Berry–Esseen itself in Lean (smoothing inequality + characteristic functions): a large
  independent project.
