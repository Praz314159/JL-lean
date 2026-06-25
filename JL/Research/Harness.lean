/-
Copyright (c) 2026. Released under Apache 2.0 license.
JL-lean: formal verification of the lattice Johnson–Lindenstrauss projection lemmas.
-/
import JL.Research.Conjecture

/-!
# A grinding harness for Conjecture 1

This file factors Conjecture 1 into (a) two **explicit, abstract tool interfaces** standing in for
the standard probability machinery — sub-exponential Bernstein concentration and Berry–Esseen
anti-concentration — and (b) a self-contained **`FeasibleSchedule`** bundling a parameter schedule
together with the *concrete inequalities* that make the two interfaces compose to the JL guarantee at
each `κ`, plus the `Θ` rate bounds.

`conjecture1_of_interfaces` then proves `Conjecture1_Statement` from `interfaces + FeasibleSchedule`.
Its proof is pure assembly — it touches no probability internals. **All the genuinely-open content
of the conjecture (the constant coordination and scaling that RoKoko hedges on) is exactly the work
of constructing a `FeasibleSchedule`: a finite list of explicit real inequalities (`exp`/`log`/`pow`
bounds and `Θ` estimates), with the deep tools abstracted away.** That construction is the grind.

The interfaces use the relative-width parameterisation: at dimension `n` and relative width `ε`, the
norm ratio `‖Jw‖₂/‖w‖₂` concentrates in `[√((n/2)(1−ε)), √((n/2)(1+ε))]` with failure `≤ 2e^{−cε²n}`
(Bernstein); the mod-`q` soundness bad event has probability `≤ pⁿ` with `p < 1` (the per-row bad
probability `p(α,β)`, held uniform — the Berry–Esseen constant claim).
-/

open MeasureTheory ProbabilityTheory Matrix Filter Topology

namespace JL.Research

/-- Lower endpoint of the concentration window at dimension `n`, relative width `ε`:
`√((n/2)(1−ε))`. -/
noncomputable def windowLo (n : ℕ) (ε : ℝ) : ℝ := Real.sqrt ((n : ℝ) / 2 * (1 - ε))

/-- Upper endpoint of the concentration window at dimension `n`, relative width `ε`:
`√((n/2)(1+ε))`. -/
noncomputable def windowHi (n : ℕ) (ε : ℝ) : ℝ := Real.sqrt ((n : ℝ) / 2 * (1 + ε))

/-- **Pillar 1 interface** — abstracts sub-exponential Bernstein / χ² concentration. With rate
constant `c`, for any χ-matrix of height `n`, nonzero `w`, and relative width `ε ∈ (0,1)`, the norm
ratio lands outside the window `[windowLo n ε, windowHi n ε]` except with probability `≤ 2e^{−cε²n}`.
(Discharged later by `SqNormConcentrationHyp` / `ChiSquaredTailHyp`.) -/
def ConcentrationInterface (c : ℝ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n m : ℕ}
    (J : Ω → Matrix (Fin n) (Fin m) ℤ), IsChiMatrix J μ → ∀ (w : Fin m → ℤ), w ≠ 0 →
      ∀ (ε : ℝ), 0 < ε → ε < 1 →
        μ.real {ω | normRatio J w ω ∉ Set.Icc (windowLo n ε) (windowHi n ε)}
          ≤ 2 * Real.exp (-(c * ε ^ 2 * (n : ℝ)))

/-- **Pillar 2 interface** — abstracts Berry–Esseen anti-concentration. With per-row bad probability
`p < 1` (held uniform over the relevant `α`, `β` — the Berry–Esseen constant claim), for any
χ-matrix of height `n`, any norm threshold `α` and modulus slack `b > 0`, and any `w ∈ [±q/2]^m` with
`‖w‖₂ ≥ θ`, `0 < θ ≤ q/b`, the mod-`q` soundness bad event `‖Jw mod q‖₂ ≤ α·θ` has probability
`≤ pⁿ` (the `n` independent rows). -/
def AntiConcentrationInterface (p : ℝ) (q : ℕ) : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n m : ℕ}
    (J : Ω → Matrix (Fin n) (Fin m) ℤ), IsChiMatrix J μ → ∀ (α b : ℝ), 0 < b →
      ∀ (w : Fin m → ℤ) (θ : ℝ), 0 < θ → θ ≤ q / b →
        (∀ j, (w j : ℝ) ∈ Set.Icc (-(q : ℝ) / 2) ((q : ℝ) / 2)) → θ ≤ l2Norm w →
          μ.real {ω | projModL2Norm J w q ω ≤ α * θ} ≤ p ^ n

/-- A **feasible parameter schedule** for rate constants `(c, p)` and modulus `q`: a schedule
`κ ↦ (n κ, α κ, β κ, b κ)` whose window matches the Pillar-1 interface at relative width `1/2`, whose
dimension makes both interface failure bounds `≤ κ`, and whose parameters obey the `Θ` rate laws.

**This bundles exactly the grindable content of Conjecture 1** — the fields are concrete real
inequalities over the schedule and the rate constants `c, p`; constructing a term of this structure
is the open scaling/coordination problem (no probability involved). -/
structure FeasibleSchedule (c p : ℝ) (q : ℕ) where
  /-- Projection-dimension schedule. -/
  n : ℝ → ℕ
  /-- Lower norm-ratio bound schedule. -/
  α : ℝ → ℝ
  /-- Upper norm-ratio bound schedule. -/
  β : ℝ → ℝ
  /-- Modulus-slack schedule. -/
  b : ℝ → ℝ
  /-- `α κ` is the Pillar-1 window's lower endpoint at relative width `1/2`. -/
  hα : ∀ κ, α κ = windowLo (n κ) (1 / 2)
  /-- `β κ` is the Pillar-1 window's upper endpoint at relative width `1/2`. -/
  hβ : ∀ κ, β κ = windowHi (n κ) (1 / 2)
  /-- The modulus slack is positive. -/
  hb_pos : ∀ κ, 0 < κ → κ < 1 → 0 < b κ
  /-- Pillar-1 (concentration) failure `2e^{−c(1/2)²n}` is `≤ κ`. -/
  hP1 : ∀ κ, 0 < κ → κ < 1 → 2 * Real.exp (-(c * (1 / 2) ^ 2 * (n κ : ℝ))) ≤ κ
  /-- Pillar-2 (anti-concentration) failure `pⁿ` is `≤ κ`. -/
  hP2 : ∀ κ, 0 < κ → κ < 1 → p ^ (n κ) ≤ κ
  /-- `n κ = Θ(log(1/κ))`. -/
  hnΘ : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ κ in 𝓝[>] (0 : ℝ),
    c₁ * Real.log (1 / κ) ≤ (n κ : ℝ) ∧ (n κ : ℝ) ≤ c₂ * Real.log (1 / κ)
  /-- `α κ = Θ(√log(1/κ))`. -/
  hαΘ : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ κ in 𝓝[>] (0 : ℝ),
    c₁ * Real.sqrt (Real.log (1 / κ)) ≤ α κ ∧ α κ ≤ c₂ * Real.sqrt (Real.log (1 / κ))
  /-- `β κ = Θ(√log(1/κ))`. -/
  hβΘ : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ κ in 𝓝[>] (0 : ℝ),
    c₁ * Real.sqrt (Real.log (1 / κ)) ≤ β κ ∧ β κ ≤ c₂ * Real.sqrt (Real.log (1 / κ))
  /-- `b κ = Θ(√log(1/κ))`. -/
  hbΘ : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ κ in 𝓝[>] (0 : ℝ),
    c₁ * Real.sqrt (Real.log (1 / κ)) ≤ b κ ∧ b κ ≤ c₂ * Real.sqrt (Real.log (1 / κ))

/-- **The harness centerpiece (PROVEN assembly).** Given the two explicit tool interfaces and a
`FeasibleSchedule`, Conjecture 1 holds. The proof is pure plumbing: at each `κ ∈ (0,1)` it feeds the
schedule's window into the concentration interface (Pillar 1) and its threshold into the
anti-concentration interface (Pillar 2), bounds both failures by `κ` via the schedule's `hP1`/`hP2`,
and reads off the `Θ` rates from the schedule. No probability internals are touched — the open
content is entirely in producing the `FeasibleSchedule`. -/
theorem conjecture1_of_interfaces {c p : ℝ} {q : ℕ}
    (hConc : ConcentrationInterface c) (hAnti : AntiConcentrationInterface p q)
    (S : FeasibleSchedule c p q) : Conjecture1_Statement q := by
  refine ⟨S.n, S.α, S.β, S.b, ?_, S.hnΘ, S.hαΘ, S.hβΘ, S.hbΘ⟩
  intro κ hκ0 hκ1
  refine ⟨?_, ?_⟩
  · -- Pillar 1: norm preservation
    intro Ω _ μ _ m J hJ w hw
    rw [S.hα κ, S.hβ κ]
    exact (hConc μ J hJ w hw (1 / 2) (by norm_num) (by norm_num)).trans (S.hP1 κ hκ0 hκ1)
  · -- Pillar 2: mod-q soundness
    intro Ω _ μ _ m J hJ w θ hθ hθb hwmem hwθ
    exact (hAnti μ J hJ (S.α κ) (S.b κ) (S.hb_pos κ hκ0 hκ1) w θ hθ hθb hwmem hwθ).trans
      (S.hP2 κ hκ0 hκ1)

end JL.Research
