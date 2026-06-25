/-
Copyright (c) 2026. Released under Apache 2.0 license.
JL-lean: formal verification of the lattice Johnson–Lindenstrauss projection lemmas.
-/
import JL.Defs

/-!
# The RoKoko / BS23 route — target statements (nodes N0–N3)

The lemma DAG of RoKoko Lemma 5/6 and BS23 Lemma 4.1/4.2, encoded in the no-`sorry` idiom
(`AGENTS.md`): each headline is a `Prop`-valued **target** `Nk_… : Prop`. When proved, add a
`theorem` (lowerCamel) discharging it and update `JL/doc/stability.md`. The intended proof path and
which Mathlib API closes each is recorded in `JL/doc/paper-to-lean-map.md`.

* `N0` `N0_RowSubgaussian`        — per-row sub-Gaussianity                (LEAF; Mathlib Hoeffding)
* `N1` `Lemma5_NormPreservation`  — RoKoko Lemma 5 (I) / BS23 Lemma 4.1    (easy half)
* `N2` `Lemma5_ModqSoundness`     — RoKoko Lemma 5 (II) / BS23 Lemma 4.2   (hard half; proof needs
                                     `JL.Analytic.BerryEsseenHyp` for Case 3)
* `N3` `Lemma6_Structured`        — RoKoko Lemma 6 (I⊗J extension)         (cheap; union bound)
-/

open MeasureTheory ProbabilityTheory Matrix

namespace JL

/-- Bundled parameters of the ring JL lemma (`n_rp, α_rp, β_rp, b` of RoKoko Lemma 5). -/
structure Params where
  /-- Projection dimension `n_rp`. -/
  n : ℕ
  /-- Lower norm-preservation constant `α_rp` (for the squared ratio). -/
  α : ℝ
  /-- Upper norm-preservation constant `β_rp`. -/
  β : ℝ
  /-- Modulus slack `b` (the `mod q` shortness threshold uses `θ ≤ q/b`). -/
  b : ℝ

/-- **N0 (leaf).** Each row inner product `⟨rᵢ, w⟩` is sub-Gaussian with parameter `‖w‖²`.
`⟨rᵢ,w⟩ = ∑ⱼ rᵢⱼ wⱼ` is a sum of independent zero-mean terms `rᵢⱼ wⱼ ∈ [-|wⱼ|, |wⱼ|]`; Hoeffding's
lemma gives each sub-Gaussian parameter `wⱼ²`, summing to `‖w‖²`.

Reachable now via `ProbabilityTheory.hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero` +
`HasSubgaussianMGF.add`. The cheapest fully-rigorous target alongside N3. -/
def N0_RowSubgaussian : Prop :=
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {n m : ℕ}
    (J : Ω → Matrix (Fin n) (Fin m) ℤ), IsChiMatrix J μ → ∀ (w : Fin m → ℤ) (i : Fin n),
      HasSubgaussianMGF (rowInner J w i) (sqNorm w).toNNReal μ

/-- **N1 (Lemma 5, inequality I — the easy half).** For any `κ ∈ (0,1)` and modulus `q` there are
parameters `(n, α, β)` so that for every width `m`, every χ-matrix `J` of height `n`, and every
nonzero `w`, the squared-norm ratio `‖Jw‖²/‖w‖²` lands in `[α, β]` except with probability `κ`.
Concretely (BS23 Lemma 4.1, `κ = 2⁻¹²⁸`): `n = 256`, `[α, β] = [30, 337]`.

Reachable in *shape* now via Hoeffding-for-sums on `‖Jw‖² = ∑ⱼ ⟨rⱼ,w⟩²` (loose constants); the
tight `[30,337]` needs sub-exponential Bernstein or `JL.Analytic.ChiSquaredTailHyp` (Gaussian model). -/
def Lemma5_NormPreservation (κ : ℝ) (q : ℕ) : Prop :=
  ∃ P : Params, 0 < P.α ∧ P.α ≤ P.β ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ}
      (J : Ω → Matrix (Fin P.n) (Fin m) ℤ), IsChiMatrix J μ → ∀ w : Fin m → ℤ, w ≠ 0 →
        μ.real {ω | ratio J w ω ∉ Set.Icc P.α P.β} ≤ κ

/-- **N2 (Lemma 5, inequality II — the hard half).** With the same parameters as N1, for
`0 < θ ≤ q/b`, any `w ∈ [±q/2]^m` with `‖w‖² ≥ θ`, the reduced projection `‖Jw mod q‖²` exceeds
`α·θ` except with probability `κ`: wrap-around mod `q` cannot make a long vector look short.

Proof (BS23 App A) splits on `w`'s geometry — Case 1 (`‖w‖<q/10`, → N1), Case 2 (`‖w‖∞≥q/60`,
Chernoff), **Case 3 (`‖w‖≥q/10 ∧ ‖w‖∞<q/60`, needs `JL.Analytic.BerryEsseenHyp`)**. The eventual
`theorem` discharging this will take `(hBE : BerryEsseenHyp)`. -/
def Lemma5_ModqSoundness (κ : ℝ) (q : ℕ) : Prop :=
  ∃ P : Params, 0 < P.α ∧ P.α ≤ P.β ∧ 0 < P.b ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ}
      (J : Ω → Matrix (Fin P.n) (Fin m) ℤ), IsChiMatrix J μ →
        ∀ (w : Fin m → ℤ) (θ : ℝ), 0 < θ → θ ≤ q / P.b →
          (∀ j, (w j : ℝ) ∈ Set.Icc (-(q : ℝ) / 2) ((q : ℝ) / 2)) → θ ≤ sqNorm w →
            μ.real {ω | projModSqNorm J w q ω ≤ P.α * θ} ≤ κ

/-- **N3 (Lemma 6).** Block-diagonal extension `V = (I ⊗ J)·W`: the per-block N1 guarantee lifts to
a multi-column witness at the cost of a union-bound factor `κ·r·blocks`. Stated as the conditional
"per-block window bound ⟹ union-bounded bound" so its proof depends only on the *statement* of N1.

Reachable now: pure structural bookkeeping + `MeasureTheory.measure_biUnion_le`. Recommended first
proof. -/
def Lemma6_Structured (κ : ℝ) (P : Params) : Prop :=
  (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ}
    (J : Ω → Matrix (Fin P.n) (Fin m) ℤ), IsChiMatrix J μ → ∀ w : Fin m → ℤ, w ≠ 0 →
      μ.real {ω | ratio J w ω ∉ Set.Icc P.α P.β} ≤ κ) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m r blocks : ℕ}
    (J : Ω → Matrix (Fin P.n) (Fin m) ℤ), IsChiMatrix J μ →
    ∀ (W : Fin r → Fin blocks → Fin m → ℤ), (∀ c i, W c i ≠ 0) →
      μ.real {ω | ∃ c i, ratio J (W c i) ω ∉ Set.Icc P.α P.β} ≤ κ * r * blocks

end JL
