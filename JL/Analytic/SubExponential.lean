/-
Copyright (c) 2026. Released under Apache 2.0 license.
JL-lean: formal verification of the lattice Johnson–Lindenstrauss projection lemmas.
-/
import JL.Defs

/-!
# Sub-exponential Bernstein concentration — a DERIVABLE analytic input

`SqNormConcentrationHyp` packages the two-sided concentration of the squared projection norm
`‖Jw‖₂² = ∑ⱼ ⟨rⱼ,w⟩²` around its mean `(n/2)·‖w‖₂²`, in **squared-ratio form**: for every target
failure probability there is a projection dimension and a multiplicative window `[a, b]` such that
`‖Jw‖₂²/‖w‖₂² ∈ [a, b]` except with that probability.

This is exactly the conclusion of **Bernstein's inequality for the sum of the i.i.d.
sub-exponential terms `⟨rⱼ,w⟩²`** (each `⟨rⱼ,w⟩` is sub-Gaussian with parameter `‖w‖₂²` — that is
`JL.n0_rowSubgaussian` — so its square is sub-exponential with an **m-independent** variance proxy).
Mathlib has no sub-exponential / Bernstein layer (`JL/doc/mathlib-audit.md`), so we expose this as a
named hypothesis. Unlike `BerryEsseenHyp`, it is **derivable** (standard, just unformalized): the
intent is to discharge it by building the sub-exponential layer, not to assume it permanently.

`JL.lemma5_norm_preservation` (Pillar 1, RoKoko Lemma 5 (I)) is proved from this hypothesis — the
ℓ₂-norm window is the `√·` image of the squared window (via `JL.l2Norm_sq`).
-/

open MeasureTheory ProbabilityTheory Matrix

namespace JL.Analytic

/-- **Two-sided concentration of `‖Jw‖₂²/‖w‖₂²` (squared-ratio form), as a named hypothesis.**

For every `κ ∈ (0,1)` there are a projection dimension `n` and a window `[a, b]` with `0 < a ≤ b`
such that for any χ-matrix `J` of height `n` and any nonzero `w`,
`Pr[ ‖Jw‖₂²/‖w‖₂² ∉ [a, b] ] ≤ κ`.

This is the sub-exponential **Bernstein** concentration of `∑ⱼ ⟨rⱼ,w⟩²` (see module docstring):
derivable from `JL.n0_rowSubgaussian` once a sub-exponential layer exists; assumed for now. -/
def SqNormConcentrationHyp : Prop :=
  ∀ {κ : ℝ}, 0 < κ → κ < 1 → ∃ (n : ℕ) (a b : ℝ), 0 < a ∧ a ≤ b ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ}
      (J : Ω → Matrix (Fin n) (Fin m) ℤ), IsChiMatrix J μ → ∀ w : Fin m → ℤ, w ≠ 0 →
        μ.real {ω | sqNorm (proj J w ω) / sqNorm w ∉ Set.Icc a b} ≤ κ

end JL.Analytic
