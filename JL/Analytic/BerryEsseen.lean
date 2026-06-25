/-
Copyright (c) 2026. Released under Apache 2.0 license.
JL-lean: formal verification of the lattice Johnson–Lindenstrauss projection lemmas.
-/
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Probability.Independence.Basic

/-!
# Berry–Esseen — THE irreducible analytic gap, as a named hypothesis

`BerryEsseenHyp` is the quantitative central limit theorem (Lyapunov form), stated as a
`Prop`-valued abbreviation. Mathlib has only a *qualitative* CLT (`TendstoInDistribution`, no rate);
the audit (`JL/doc/mathlib-audit.md` §3a) confirmed Berry–Esseen is absent. Rather than `sorry` it,
we expose it as an explicit hypothesis: every downstream result that needs it takes
`(hBE : BerryEsseenHyp)` as an argument, so the dependency is type-enforced and visible, and the
build stays `sorry`-free (see `AGENTS.md`).

This is exactly where RoKoko Conjecture 1 and BS23 Lemma 4.2 Case 3 live: the anti-concentration
argument that a projection row is "bad" with probability `p = 0.39 + 2·0.15 < 1` rests on bounding
`|Pr[⟨π,v⟩ ≤ x] − Pr[Y ≤ x]|` by the Berry–Esseen rate, `Y` Gaussian with the matching variance.

Discharging `BerryEsseenHyp` means either Mathlib gains a quantitative CLT, or we add a self-contained
Lean proof under `References/BerryEsseen/Spec.lean` (smoothing inequality + characteristic-function
estimates — a large independent project).
-/

open MeasureTheory ProbabilityTheory

namespace JL.Analytic

/-- The Berry–Esseen / Esseen constant. Best known absolute constant `≤ 0.5600`
(Korolev–Shevtsova). Kept named so the downstream constant bookkeeping (`p(α,β) < 1`) is explicit. -/
def esseenConst : ℝ := 0.56

/-- **Berry–Esseen theorem (Lyapunov / independent-but-not-identical form), as a named hypothesis.**

For independent, mean-zero, square-integrable real random variables `X i` (`i : ι` finite) with
variances `σ i ^ 2 > 0`, absolute third moments `ρ i`, and per-summand Lyapunov ratio bounded by
`L`, the CDF of the sum `S = ∑ i, X i` is uniformly close to that of a centered Gaussian with
variance `v = ∑ i, σ i ^ 2`:
`|Pr[S ≤ x] − Pr[Y ≤ x]| ≤ esseenConst · L / √v`.

This matches the form used in BS23 Appendix A (Case 3). It is the project's single irreducible
analytic input; see the module docstring. -/
def BerryEsseenHyp : Prop :=
  ∀ {Ω ι : Type} [Fintype ι] {_ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (X : ι → Ω → ℝ), iIndepFun X μ → (∀ i, AEMeasurable (X i) μ) →
    (∀ i, ∫ ω, X i ω ∂μ = 0) →
    ∀ (σ : ι → ℝ), (∀ i, 0 < σ i) → (∀ i, ∫ ω, (X i ω) ^ 2 ∂μ = (σ i) ^ 2) →
    ∀ (ρ : ι → ℝ), (∀ i, ∫ ω, |X i ω| ^ 3 ∂μ = ρ i) →
    ∀ (L : ℝ), (∀ i, ρ i / (σ i) ^ 2 ≤ L) →
    ∀ (v : NNReal), (v : ℝ) = ∑ i, (σ i) ^ 2 →
    ∀ x : ℝ, |μ.real {ω | (∑ i, X i ω) ≤ x} - (gaussianReal 0 v).real (Set.Iic x)|
      ≤ esseenConst * L / Real.sqrt v

end JL.Analytic
