/-
Copyright (c) 2026. Released under Apache 2.0 license.
JL-lean: formal verification of the lattice Johnson–Lindenstrauss projection lemmas.
-/
import JL.Defs

/-!
# The LNP22 "approximate range proof" route — target statements (Berry–Esseen-FREE)

The JL projection results of [LNP22], which prove the mod-`q` soundness **without** any Berry–Esseen
anti-concentration step (see `JL/doc/paper-to-lean-map.md` §2b and `JL/doc/mathlib-audit.md`). The
price is an **m-dependent** modulus threshold `b ≤ P/(41m)` (vs. BS23's m-independent `q/125`), so
RoKoko Conjecture 1 cannot use it — but the route is fully rigorous, Lean-friendly, and relocates the
only remaining gap onto `JL.Analytic.ChiSquaredTailHyp` instead of Berry–Esseen.

Encoded as `Prop`-valued targets (`AGENTS.md` no-`sorry` idiom):

* `L7`  `Arp_Linf`            — Lemma 2.7, ℓ∞ approximate range proof (PROVEN leaf, [LNS21a])
* `L10` `Lnp_ModqUnmasked`    — Lemma 2.10, unmasked mod-q soundness for Bin₂ (proof bottoms at L8/χ²)
* `L9a` `Symmetrization`      — the Bin₁−Bin₁=Bin₂ reduction (L10 ⟹ L9), fully rigorous
* `L9`  `Lnp_ModqMasked`      — Lemma 2.9, masked mod-q soundness for χ=Bin₁ (the protocol form)
-/

open MeasureTheory ProbabilityTheory Matrix

namespace JL

/-- **L7 (LNP22 Lemma 2.7 — PROVEN leaf target).** For `R ← χ^{k×m}` and any mask `ŷ`,
`Pr[ ‖Rw + ŷ‖∞ < ½‖w‖∞ ] ≤ 2^{-k}`.

Fully rigorous and elementary (no Gaussian/χ²/Berry–Esseen): per row, after fixing all but the
coordinate attaining `‖w‖∞`, at most one of the three χ-values keeps the inner product below
`½‖w‖∞`, and `Pr` of "two of three" is `≥ 1/2`; independence over the `k` rows gives `2^{-k}`. A
clean self-contained first target. -/
def Arp_Linf : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {k m : ℕ}
    (R : Ω → Matrix (Fin k) (Fin m) ℤ), IsChiMatrix R μ → ∀ (w : Fin m → ℤ) (yhat : Fin k → ℤ),
      μ.real {ω | (normInf ((R ω *ᵥ w) + yhat) : ℝ) < (normInf w : ℝ) / 2} ≤ (2 : ℝ) ^ (-(k : ℤ))

/-- **L10 (LNP22 Lemma 2.10).** For `R ← Bin₂^{256×m}`, `b ≤ P/(41m)`, `w ∈ [±P/2]^m`, `‖w‖ ≥ b`:
`Pr[ ‖Rw mod P‖ < b·√26 ] < 2^{-256}`.

Two-case proof: `‖w‖∞ ≥ P/(4m)` → elementary Chernoff `(1/2)^256` (no anti-concentration);
`‖w‖∞ < P/(4m)` → mod-`P` reduction is inert and the bound follows from the χ² norm bound
(`JL.Analytic.ChiSquaredTailHyp`). So L10's only non-elementary input is χ², not Berry–Esseen. -/
def Lnp_ModqUnmasked : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (P : ℕ)
    (R : Ω → Matrix (Fin 256) (Fin m) ℤ), IsBin2Matrix R μ →
    ∀ (b : ℝ), 0 < b → b ≤ (P : ℝ) / (41 * m) → ∀ (w : Fin m → ℤ),
      (∀ j, (w j : ℝ) ∈ Set.Icc (-(P : ℝ) / 2) ((P : ℝ) / 2)) → b ^ 2 ≤ sqNorm w →
        μ.real {ω | sqNorm (fun i => centeredMod P ((R ω *ᵥ w) i)) < (b * Real.sqrt 26) ^ 2}
          < (2 : ℝ) ^ (-(256 : ℤ))

/-- **L9 (LNP22 Lemma 2.9 — masked mod-q soundness, the protocol form).** For `R ← χ=Bin₁^{256×m}`,
`b ≤ P/(41m)`, `w ∈ [±P/2]^m` with `‖w‖ ≥ b`, and **any** mask `ŷ ∈ ℤ_P^{256}`:
`Pr[ ‖Rw + ŷ mod P‖ < ½·b·√26 ] < 2^{-128}`.

The generalization of BS23 Lemma 4.2 that lattice-ZK protocols invoke (masked projection with
rejection sampling). Follows from `Lnp_ModqUnmasked` (L10) via `Symmetrization` (L9a); its only
non-elementary dependency is the χ² norm bound, NOT Berry–Esseen. -/
def Lnp_ModqMasked : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ} (P : ℕ)
    (R : Ω → Matrix (Fin 256) (Fin m) ℤ), IsChiMatrix R μ →
    ∀ (b : ℝ), 0 < b → b ≤ (P : ℝ) / (41 * m) → ∀ (w : Fin m → ℤ),
      (∀ j, (w j : ℝ) ∈ Set.Icc (-(P : ℝ) / 2) ((P : ℝ) / 2)) → b ^ 2 ≤ sqNorm w →
      ∀ yhat : Fin 256 → ℤ,
        μ.real {ω | maskedProjModSqNorm R w yhat P ω < (b * Real.sqrt 26 / 2) ^ 2}
          < (2 : ℝ) ^ (-(128 : ℤ))

/-- **L9a (the symmetrization trick — fully rigorous, the heart of the Berry–Esseen-free route).**
The masked, Bin₁ soundness (L9) reduces to the unmasked, Bin₂ soundness (L10): two independent
copies `R₁,R₂ ← χ`, triangle inequality (valid mod `P`), and `R₁ − R₂ ~ Bin₂`. Stated as the
implication "`Lnp_ModqUnmasked` ⟹ `Lnp_ModqMasked`" to make the reduction explicit. No Gaussian
approximation. -/
def Symmetrization : Prop := Lnp_ModqUnmasked → Lnp_ModqMasked

end JL
