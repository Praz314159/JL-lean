/-
Copyright (c) 2026. Released under Apache 2.0 license.
JL-lean: formal verification of the lattice Johnson–Lindenstrauss projection lemmas.
-/
import Mathlib.Probability.Distributions.Gamma
import Mathlib.Probability.Notation

/-!
# χ² tail bounds — a DERIVABLE analytic input, as a named hypothesis

`ChiSquaredTailHyp` packages the standard two-sided (Laurent–Massart) tail bound for a
χ²-distributed variable with `n` degrees of freedom. It is the norm-window input for the
Gaussian-model route (LNP22 Lemma 2.8; RoKoko App A's "rigorous Gaussian analog", where
`‖Jw‖² = ½‖w‖²·χ²_n`).

Unlike `BerryEsseenHyp`, this is **derivable in-tree**: `χ²_n = Gamma(n/2, 1/2)` (shape `n/2`, rate
`1/2`), and Mathlib has `gammaMeasure` plus MGF/Chernoff machinery (`JL/doc/mathlib-audit.md` §3c).
It is exposed as a hypothesis now to keep the build `sorry`-free while the derivation is pending; the
intent is to replace it with a proved `theorem` discharging this `Prop`, not to assume it forever.
-/

open MeasureTheory ProbabilityTheory

namespace JL.Analytic

/-- **Two-sided χ² tail bound (Laurent–Massart), as a named hypothesis.**

If `Y` is χ²ₙ-distributed (its law is `gammaMeasure (n/2) (1/2)`, mean `n`), then for every `t ≥ 0`:
`Pr[Y ≤ n − 2√(n·t)] ≤ e^{-t}` and `Pr[Y ≥ n + 2√(n·t) + 2t] ≤ e^{-t}`.

This is the standard, rigorous form (Laurent–Massart 2000) and is exactly what a Mathlib `Gamma`
+ Chernoff derivation would establish. Instantiating it yields the LNP22 Lemma 2.8 norm window
(`Pr[χ²₂₅₆ < 26]`, `Pr[χ²₂₅₆ > 674]`) and hence `[√30, √337]`. Assumed pending the derivation. -/
def ChiSquaredTailHyp : Prop :=
  ∀ {Ω : Type} {_ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
    (Y : Ω → ℝ) (n : ℕ),
    μ.map Y = gammaMeasure (n / 2 : ℝ) (1 / 2 : ℝ) →
    ∀ t : ℝ, 0 ≤ t →
      μ.real {ω | Y ω ≤ (n : ℝ) - 2 * Real.sqrt (n * t)} ≤ Real.exp (-t) ∧
      μ.real {ω | (n : ℝ) + 2 * Real.sqrt (n * t) + 2 * t ≤ Y ω} ≤ Real.exp (-t)

end JL.Analytic
