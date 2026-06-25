/-
Copyright (c) 2026. Released under Apache 2.0 license.
JL-lean: formal verification of the lattice Johnson–Lindenstrauss projection lemmas.
-/
import JL.Research.Harness

/-!
# First grinding pass: an explicit schedule with the failure bounds discharged

A concrete candidate `FeasibleSchedule` (see `JL/Research/Harness.lean`): the dimension schedule
`n κ = ⌈M·log(2/κ)⌉` with `M = max(4/c, 1/log(1/p))`, window `α κ = √(n/4)`, `β κ = √(3n/4)`,
slack `b κ = √n`.

**This pass discharges the two failure-bound obligations** — `hP1` (`2e^{−c(1/2)²n} ≤ κ`) and `hP2`
(`pⁿ ≤ κ`) — by the explicit `exp`/`log` calculation: `M ≥ 4/c` makes the concentration tail close,
`M ≥ 1/log(1/p)` makes the anti-concentration tail close. The plumbing (`hα`/`hβ`/`hb_pos`) is also
proved. The four `Θ`-rate obligations are left as explicit premises of `grindSchedule` — the next
grind chunk (`Nat.ceil` + `log`/`sqrt` estimates, eventually as `κ → 0⁺`).
-/

open Real Filter Topology

namespace JL.Research

/-- Rate-balancing constant `M = max(4/c, 1/log(1/p))`: large enough that one dimension schedule
satisfies *both* tail requirements. -/
noncomputable def grindM (c p : ℝ) : ℝ := max (4 / c) (1 / Real.log (1 / p))

/-- Candidate dimension schedule `n κ = ⌈M · log(2/κ)⌉`. -/
noncomputable def grindDim (c p : ℝ) (κ : ℝ) : ℕ := ⌈grindM c p * Real.log (2 / κ)⌉₊

variable {c p : ℝ}

/-- `log(2/κ) > 0` for `κ ∈ (0,1)` (indeed `2/κ > 2 > 1`). -/
theorem log_two_div_pos {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) : 0 < Real.log (2 / κ) :=
  Real.log_pos ((one_lt_div hκ0).mpr (by linarith))

/-- `log(1/p) > 0` for `p ∈ (0,1)`. -/
theorem log_one_div_pos (hp0 : 0 < p) (hp1 : p < 1) : 0 < Real.log (1 / p) :=
  Real.log_pos ((one_lt_div hp0).mpr hp1)

/-- `M > 0`. -/
theorem grindM_pos (hc : 0 < c) : 0 < grindM c p :=
  lt_max_of_lt_left (by positivity)

/-- The defining lower bound: `M · log(2/κ) ≤ n κ`. -/
theorem grindM_log_le (κ : ℝ) : grindM c p * Real.log (2 / κ) ≤ (grindDim c p κ : ℝ) :=
  Nat.le_ceil _

/-- `n κ > 0` for `κ ∈ (0,1)`. -/
theorem grindDim_pos (hc : 0 < c) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    0 < grindDim c p κ :=
  Nat.ceil_pos.mpr (mul_pos (grindM_pos hc) (log_two_div_pos hκ0 hκ1))

/-- **Pillar-2 failure bound discharged**: `pⁿ ≤ κ`. Since `n ≥ (1/log(1/p))·log(2/κ) ≥
(1/log(1/p))·log(1/κ)`, we get `n·log(1/p) ≥ log(1/κ)`, hence `pⁿ = e^{−n·log(1/p)} ≤ e^{log κ} = κ`. -/
theorem grind_hP2 (hp0 : 0 < p) (hp1 : p < 1) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    p ^ (grindDim c p κ) ≤ κ := by
  have hL : 0 < Real.log (1 / p) := log_one_div_pos hp0 hp1
  have hlogp : Real.log p = -Real.log (1 / p) := by
    rw [Real.log_div one_ne_zero (ne_of_gt hp0), Real.log_one]; ring
  -- `log(1/κ) ≤ n · log(1/p)`
  have hkey : Real.log (1 / κ) ≤ (grindDim c p κ : ℝ) * Real.log (1 / p) := by
    have h1 : (1 / Real.log (1 / p)) * Real.log (1 / κ) ≤ (grindDim c p κ : ℝ) := by
      refine le_trans ?_ (grindM_log_le κ)
      have hmono : Real.log (1 / κ) ≤ Real.log (2 / κ) :=
        Real.log_le_log (by positivity) (by rw [div_le_div_iff_of_pos_right hκ0]; linarith)
      calc (1 / Real.log (1 / p)) * Real.log (1 / κ)
          ≤ (1 / Real.log (1 / p)) * Real.log (2 / κ) := by
            apply mul_le_mul_of_nonneg_left hmono (by positivity)
        _ ≤ grindM c p * Real.log (2 / κ) := by
            apply mul_le_mul_of_nonneg_right (le_max_right _ _)
              (le_of_lt (log_two_div_pos hκ0 hκ1))
    have hmul := mul_le_mul_of_nonneg_right h1 hL.le
    rwa [mul_comm (1 / Real.log (1 / p)) (Real.log (1 / κ)), mul_assoc,
      one_div_mul_cancel (ne_of_gt hL), mul_one] at hmul
  calc p ^ (grindDim c p κ)
      = Real.exp (Real.log p * (grindDim c p κ : ℝ)) := by
        rw [← Real.rpow_natCast p (grindDim c p κ), Real.rpow_def_of_pos hp0]
    _ ≤ κ := by
        rw [hlogp]
        rw [show -Real.log (1 / p) * (grindDim c p κ : ℝ)
            = -((grindDim c p κ : ℝ) * Real.log (1 / p)) by ring]
        calc Real.exp (-((grindDim c p κ : ℝ) * Real.log (1 / p)))
            ≤ Real.exp (-Real.log (1 / κ)) := by
              apply Real.exp_le_exp.mpr; linarith
          _ = κ := by rw [one_div, Real.log_inv, neg_neg, Real.exp_log hκ0]

/-- **Pillar-1 failure bound discharged**: `2e^{−c(1/2)²n} ≤ κ`. Since `n ≥ (4/c)·log(2/κ)`, we get
`(c/4)·n ≥ log(2/κ)`, hence `e^{−(c/4)n} ≤ e^{log(κ/2)} = κ/2`, and doubling gives `≤ κ`. -/
theorem grind_hP1 (hc : 0 < c) {κ : ℝ} (hκ0 : 0 < κ) (hκ1 : κ < 1) :
    2 * Real.exp (-(c * (1 / 2) ^ 2 * (grindDim c p κ : ℝ))) ≤ κ := by
  -- `log(2/κ) ≤ (c/4) · n`
  have hkey : Real.log (2 / κ) ≤ c / 4 * (grindDim c p κ : ℝ) := by
    have h1 : (4 / c) * Real.log (2 / κ) ≤ (grindDim c p κ : ℝ) :=
      le_trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (le_of_lt (log_two_div_pos hκ0 hκ1))) (grindM_log_le κ)
    have hmul := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ c / 4)
    rwa [show c / 4 * (4 / c * Real.log (2 / κ)) = Real.log (2 / κ) by
      field_simp] at hmul
  have hexp : Real.exp (-(c * (1 / 2) ^ 2 * (grindDim c p κ : ℝ))) ≤ κ / 2 := by
    rw [show -(c * (1 / 2) ^ 2 * (grindDim c p κ : ℝ)) = -(c / 4 * (grindDim c p κ : ℝ)) by ring]
    calc Real.exp (-(c / 4 * (grindDim c p κ : ℝ)))
        ≤ Real.exp (-Real.log (2 / κ)) := by apply Real.exp_le_exp.mpr; linarith
      _ = κ / 2 := by rw [← Real.log_inv, inv_div, Real.exp_log (by positivity)]
  linarith [hexp]

/-- **`Θ`-rate for the dimension discharged**: `n κ = ⌈M·log(2/κ)⌉ = Θ(log(1/κ))`. Lower bound
`M·log(1/κ) ≤ n κ` holds throughout (`Nat.le_ceil` + `log(2/κ) ≥ log(1/κ)`); upper bound
`n κ ≤ (M+1)·log(1/κ)` holds eventually (`Nat.ceil_lt_add_one`, plus `log(1/κ) > M·log2 + 1` once
`κ < e^{−(M·log2+1)}`). -/
theorem grind_hnΘ (hc : 0 < c) :
    ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ κ in 𝓝[>] (0 : ℝ),
      c₁ * Real.log (1 / κ) ≤ (grindDim c p κ : ℝ) ∧
        (grindDim c p κ : ℝ) ≤ c₂ * Real.log (1 / κ) := by
  have hMpos : 0 < grindM c p := grindM_pos hc
  refine ⟨grindM c p, grindM c p + 1, hMpos, by linarith, ?_⟩
  have hεpos : 0 < Real.exp (-(grindM c p * Real.log 2 + 1)) := Real.exp_pos _
  apply Filter.eventually_of_mem
    (Ioo_mem_nhdsGT_of_mem (⟨le_refl 0, hεpos⟩ :
      (0 : ℝ) ∈ Set.Ico 0 (Real.exp (-(grindM c p * Real.log 2 + 1)))))
  intro κ hκ
  obtain ⟨hκ0, hκε⟩ := hκ
  have hε1 : Real.exp (-(grindM c p * Real.log 2 + 1)) < 1 := by
    have hneg : -(grindM c p * Real.log 2 + 1) < 0 := by
      nlinarith [mul_pos hMpos (Real.log_pos one_lt_two)]
    calc Real.exp (-(grindM c p * Real.log 2 + 1)) < Real.exp 0 := Real.exp_lt_exp.mpr hneg
      _ = 1 := Real.exp_zero
  have hκ1 : κ < 1 := lt_trans hκε hε1
  have hlog2κ : 0 < Real.log (2 / κ) := log_two_div_pos hκ0 hκ1
  have hmono : Real.log (1 / κ) ≤ Real.log (2 / κ) :=
    Real.log_le_log (by positivity) (by rw [div_le_div_iff_of_pos_right hκ0]; linarith)
  refine ⟨?_, ?_⟩
  · calc grindM c p * Real.log (1 / κ)
        ≤ grindM c p * Real.log (2 / κ) := mul_le_mul_of_nonneg_left hmono hMpos.le
      _ ≤ (grindDim c p κ : ℝ) := grindM_log_le κ
  · have hceil : (grindDim c p κ : ℝ) < grindM c p * Real.log (2 / κ) + 1 :=
      Nat.ceil_lt_add_one (mul_nonneg hMpos.le hlog2κ.le)
    have hlog2κ_eq : Real.log (2 / κ) = Real.log 2 + Real.log (1 / κ) := by
      rw [Real.log_div two_ne_zero (ne_of_gt hκ0), one_div, Real.log_inv]; ring
    have hbig : grindM c p * Real.log 2 + 1 < Real.log (1 / κ) := by
      rw [one_div, Real.log_inv]
      have hlogκ : Real.log κ < -(grindM c p * Real.log 2 + 1) := by
        have h := Real.log_lt_log hκ0 hκε; rwa [Real.log_exp] at h
      linarith
    calc (grindDim c p κ : ℝ)
        ≤ grindM c p * Real.log (2 / κ) + 1 := le_of_lt hceil
      _ = grindM c p * Real.log 2 + grindM c p * Real.log (1 / κ) + 1 := by rw [hlog2κ_eq]; ring
      _ ≤ (grindM c p + 1) * Real.log (1 / κ) := by nlinarith [hbig]

/-- **First grinding pass — a concrete `FeasibleSchedule`** for the explicit schedule
`n κ = ⌈M·log(2/κ)⌉`, `α = √(n/4)`, `β = √(3n/4)`, `b = √n`. The two failure bounds (`hP1`, `hP2`),
the dimension rate (`hnΘ`, via `grind_hnΘ`), and the plumbing (`hα`/`hβ`/`hb_pos`) are **proved**;
the three `√`-image rate obligations (`hαΘ`/`hβΘ`/`hbΘ`) remain explicit premises — the next grind
chunk. Feeding this to `conjecture1_of_interfaces` yields `Conjecture1_Statement q`. -/
noncomputable def grindSchedule (q : ℕ) (hc : 0 < c) (hp0 : 0 < p) (hp1 : p < 1)
    (hαΘ : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ κ in 𝓝[>] (0 : ℝ),
      c₁ * Real.sqrt (Real.log (1 / κ)) ≤ windowLo (grindDim c p κ) (1 / 2) ∧
        windowLo (grindDim c p κ) (1 / 2) ≤ c₂ * Real.sqrt (Real.log (1 / κ)))
    (hβΘ : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ κ in 𝓝[>] (0 : ℝ),
      c₁ * Real.sqrt (Real.log (1 / κ)) ≤ windowHi (grindDim c p κ) (1 / 2) ∧
        windowHi (grindDim c p κ) (1 / 2) ≤ c₂ * Real.sqrt (Real.log (1 / κ)))
    (hbΘ : ∃ c₁ c₂ : ℝ, 0 < c₁ ∧ 0 < c₂ ∧ ∀ᶠ κ in 𝓝[>] (0 : ℝ),
      c₁ * Real.sqrt (Real.log (1 / κ)) ≤ Real.sqrt (grindDim c p κ) ∧
        Real.sqrt (grindDim c p κ) ≤ c₂ * Real.sqrt (Real.log (1 / κ))) :
    FeasibleSchedule c p q where
  n := grindDim c p
  α := fun κ => windowLo (grindDim c p κ) (1 / 2)
  β := fun κ => windowHi (grindDim c p κ) (1 / 2)
  b := fun κ => Real.sqrt (grindDim c p κ)
  hα := fun _ => rfl
  hβ := fun _ => rfl
  hb_pos := fun _ hκ0 hκ1 =>
    Real.sqrt_pos.mpr (Nat.cast_pos.mpr (grindDim_pos hc hκ0 hκ1))
  hP1 := fun _ hκ0 hκ1 => grind_hP1 hc hκ0 hκ1
  hP2 := fun _ hκ0 hκ1 => grind_hP2 hp0 hp1 hκ0 hκ1
  hnΘ := grind_hnΘ hc
  hαΘ := hαΘ
  hβΘ := hβΘ
  hbΘ := hbΘ

end JL.Research
