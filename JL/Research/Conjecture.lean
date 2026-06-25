/-
Copyright (c) 2026. Released under Apache 2.0 license.
JL-lean: formal verification of the lattice Johnson–Lindenstrauss projection lemmas.
-/
import JL.RoKoko
import JL.Regime
import JL.Analytic.BerryEsseen

/-!
# Conjecture 1 — asymptotic JL scaling (research / conjectured)

**Stability: research / conjectured.** RoKoko Conjecture 1, the OPEN target.

The statement is made **non-vacuous**: it asserts a parameter *schedule* `κ ↦ (n κ, α κ, β κ, b κ)`
that (i) actually *achieves* the ring-JL guarantee (Lemma 5 (I)+(II), via `AchievesJL`) at each
failure level `κ`, AND (ii) scales as `n κ = Θ(log(1/κ))`, `α κ, β κ, b κ = Θ(√log(1/κ))`. (A bare
"functions with these growth rates exist" — the original skeleton — is trivially true and says
nothing; the content is the *coupling* of the rates to the JL guarantee.)

`conjecture1_of_jlScaling` then proves the conjecture from `JLScalingHyp`: the existence of such a
schedule with *explicit* (pointwise) rate constants. The proved content is the Landau packaging
(pointwise `∀κ∈(0,1)` bounds ↦ `Θ` as `κ → 0⁺`). The residual — discharging `JLScalingHyp` — is the
genuinely conjectural part: it reduces to Pillar 1 (norm-preservation scaling, derivable via N1 +
sub-exponential Bernstein) and Pillar 2 (mod-q scaling, whose Case 3 needs `BerryEsseenHyp` with the
per-row constant `p(α,β) < 1` held uniform across the regime — the one place RoKoko itself hedges).

This is in the `JL.Research` library: built in CI, **not** pulled in by `import JL`.
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

namespace JL.Research

/-- `P` achieves the ring-JL guarantee at failure level `κ` and modulus `q`: both Lemma 5 (I)
(norm preservation, `normRatio ∈ [α, β]`) and Lemma 5 (II) (mod-`q` soundness) hold with the
parameters `P`, each except with probability `κ`. This is the per-`P` body underlying the
existential targets `Lemma5_NormPreservation` / `Lemma5_ModqSoundness`. -/
def AchievesJL (P : Params) (κ : ℝ) (q : ℕ) : Prop :=
  (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ}
      (J : Ω → Matrix (Fin P.n) (Fin m) ℤ), IsChiMatrix J μ → ∀ w : Fin m → ℤ, w ≠ 0 →
        μ.real {ω | normRatio J w ω ∉ Set.Icc P.α P.β} ≤ κ)
  ∧ (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ}
      (J : Ω → Matrix (Fin P.n) (Fin m) ℤ), IsChiMatrix J μ →
        ∀ (w : Fin m → ℤ) (θ : ℝ), 0 < θ → θ ≤ q / P.b →
          (∀ j, (w j : ℝ) ∈ Set.Icc (-(q : ℝ) / 2) ((q : ℝ) / 2)) → θ ≤ l2Norm w →
            μ.real {ω | projModL2Norm J w q ω ≤ P.α * θ} ≤ κ)

/-- **Conjecture 1 (asymptotic Johnson–Lindenstrauss scaling), non-vacuous form.**
There is a schedule `κ ↦ (n κ, α κ, β κ, b κ)` of Lemma 5 parameters that achieves the JL guarantee
at every `κ ∈ (0,1)` AND scales as `n κ = Θ(log(1/κ))`, `α κ, β κ, b κ = Θ(√log(1/κ))` as `κ → 0⁺`. -/
def Conjecture1_Statement (q : ℕ) : Prop :=
  ∃ (n : ℝ → ℕ) (α β b : ℝ → ℝ),
    (∀ κ : ℝ, 0 < κ → κ < 1 → AchievesJL ⟨n κ, α κ, β κ, b κ⟩ κ q) ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ κ in 𝓝[>] (0 : ℝ),
      c₁ * Real.log (1 / κ) ≤ (n κ : ℝ) ∧ (n κ : ℝ) ≤ c₂ * Real.log (1 / κ)) ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ κ in 𝓝[>] (0 : ℝ),
      c₁ * Real.sqrt (Real.log (1 / κ)) ≤ α κ ∧ α κ ≤ c₂ * Real.sqrt (Real.log (1 / κ))) ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ κ in 𝓝[>] (0 : ℝ),
      c₁ * Real.sqrt (Real.log (1 / κ)) ≤ β κ ∧ β κ ≤ c₂ * Real.sqrt (Real.log (1 / κ))) ∧
    (∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ κ in 𝓝[>] (0 : ℝ),
      c₁ * Real.sqrt (Real.log (1 / κ)) ≤ b κ ∧ b κ ≤ c₂ * Real.sqrt (Real.log (1 / κ)))

/-- **`JLScalingHyp` — the sharp scaling premise (the conjecture's load-bearing content).**
There is a schedule achieving the JL guarantee at every `κ ∈ (0,1)`, with *explicit* (pointwise)
`Θ` rate bounds: `n κ ∈ [c₁ log(1/κ), c₂ log(1/κ)]` and `α κ, β κ, b κ ∈ [d₁ √log(1/κ), d₂ √log(1/κ)]`.

Discharging this is the residual conjectural work: it reduces to N1 + sub-exponential Bernstein
(Pillar 1, derivable) and N2 with `JL.Analytic.BerryEsseenHyp` + the uniform `p(α,β) < 1` claim
(Pillar 2 / Case 3 — the genuinely open nub). `conjecture1_of_jlScaling` proves the conjecture from
it. -/
def JLScalingHyp (q : ℕ) : Prop :=
  ∃ (n : ℝ → ℕ) (α β b : ℝ → ℝ) (c₁ c₂ d₁ d₂ : ℝ),
    0 < c₁ ∧ 0 < c₂ ∧ 0 < d₁ ∧ 0 < d₂ ∧
    (∀ κ : ℝ, 0 < κ → κ < 1 → AchievesJL ⟨n κ, α κ, β κ, b κ⟩ κ q) ∧
    (∀ κ : ℝ, 0 < κ → κ < 1 →
      (c₁ * Real.log (1 / κ) ≤ (n κ : ℝ) ∧ (n κ : ℝ) ≤ c₂ * Real.log (1 / κ)) ∧
      (d₁ * Real.sqrt (Real.log (1 / κ)) ≤ α κ ∧ α κ ≤ d₂ * Real.sqrt (Real.log (1 / κ))) ∧
      (d₁ * Real.sqrt (Real.log (1 / κ)) ≤ β κ ∧ β κ ≤ d₂ * Real.sqrt (Real.log (1 / κ))) ∧
      (d₁ * Real.sqrt (Real.log (1 / κ)) ≤ b κ ∧ b κ ≤ d₂ * Real.sqrt (Real.log (1 / κ))))

/-- The interval `(0,1)` is a right-neighbourhood of `0`, so pointwise facts on `(0,1)` hold
eventually as `κ → 0⁺`. -/
theorem Ioo_zero_one_mem : Set.Ioo (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) :=
  Ioo_mem_nhdsGT_of_mem ⟨le_refl 0, one_pos⟩

/-- **Conjecture 1 reduced to the scaling premise (PROVEN reduction).** Given a schedule achieving
the JL guarantee with explicit pointwise `Θ` rates (`JLScalingHyp`), the conjecture holds: bundle
the schedule and convert the pointwise rate bounds on `(0,1)` to `Θ` statements as `κ → 0⁺`. The
analytic substance is isolated in `JLScalingHyp` (→ `BerryEsseenHyp` + Bernstein scaling); this
theorem is the Landau packaging. -/
theorem conjecture1_of_jlScaling {q : ℕ} (h : JLScalingHyp q) : Conjecture1_Statement q := by
  obtain ⟨n, α, β, b, c₁, c₂, d₁, d₂, hc₁, hc₂, hd₁, hd₂, hJL, hrate⟩ := h
  refine ⟨n, α, β, b, hJL, ⟨c₁, c₂, hc₁, hc₂, ?_⟩, ⟨d₁, d₂, hd₁, hd₂, ?_⟩,
    ⟨d₁, d₂, hd₁, hd₂, ?_⟩, ⟨d₁, d₂, hd₁, hd₂, ?_⟩⟩
  · exact eventually_of_mem Ioo_zero_one_mem fun κ hκ => (hrate κ hκ.1 hκ.2).1
  · exact eventually_of_mem Ioo_zero_one_mem fun κ hκ => (hrate κ hκ.1 hκ.2).2.1
  · exact eventually_of_mem Ioo_zero_one_mem fun κ hκ => (hrate κ hκ.1 hκ.2).2.2.1
  · exact eventually_of_mem Ioo_zero_one_mem fun κ hκ => (hrate κ hκ.1 hκ.2).2.2.2

/-- The regime tag for Conjecture 1: `conjectured`. -/
def conjecture1Regime : JL.JLRegime := JL.JLRegime.conjectured

end JL.Research
