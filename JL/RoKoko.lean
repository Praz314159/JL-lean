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
open scoped NNReal

namespace JL

/-- Bundled parameters of the ring JL lemma (`n_rp, α_rp, β_rp, b` of RoKoko Lemma 5). All bounds
are on the **ℓ₂ norm ratio** `‖Jw‖₂/‖w‖₂` (concretely `[α, β] = [√30, √337]`), per the paper. -/
structure Params where
  /-- Projection dimension `n_rp`. -/
  n : ℕ
  /-- Lower norm-ratio bound `α_rp` (on `‖Jw‖₂/‖w‖₂`); concretely `√30`. -/
  α : ℝ
  /-- Upper norm-ratio bound `β_rp` (on `‖Jw‖₂/‖w‖₂`); concretely `√337`. -/
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

/-- **N0 proved** (PROVEN — per-row sub-Gaussianity, the leaf). The row inner product
`⟨rᵢ,w⟩ = ∑ⱼ rᵢⱼ·wⱼ` is a sum of independent zero-mean terms, each bounded in `[-|wⱼ|, |wⱼ|]`, hence
sub-Gaussian with parameter `wⱼ²` (Hoeffding's lemma); summing over the independent coordinates
gives parameter `∑ⱼ wⱼ² = ‖w‖₂²`. -/
theorem n0_rowSubgaussian : N0_RowSubgaussian := by
  intro Ω _ μ _ n m J hJ w i
  classical
  -- (1) Independence of the row-`i` entries, then of the witness-scaled family.
  have hg : Function.Injective (fun j : Fin m => ((i, j) : Fin n × Fin m)) :=
    fun a b h => by simpa using h
  have hentryIndep : iIndepFun (fun j : Fin m => fun ω => ((J ω i j : ℤ) : ℝ)) μ := by
    simpa using hJ.indep.precomp hg
  have hXindep : iIndepFun (fun j : Fin m => fun ω => ((J ω i j : ℤ) : ℝ) * (w j : ℝ)) μ := by
    have h := hentryIndep.comp (fun j (x : ℝ) => x * (w j : ℝ))
      (fun j => measurable_id.mul_const _)
    simpa [Function.comp_def] using h
  -- (2) Each scaled entry is sub-Gaussian (bounded in `[-|wⱼ|,|wⱼ|]`, mean zero — Hoeffding).
  have hsubG : ∀ j ∈ (Finset.univ : Finset (Fin m)),
      HasSubgaussianMGF (fun ω => ((J ω i j : ℤ) : ℝ) * (w j : ℝ))
        ((‖|(w j : ℝ)| - -|(w j : ℝ)|‖₊ / 2) ^ 2) μ := by
    intro j _
    have hentry := hJ.entry (i, j)
    have hmz : (∫ ω, ((J ω i j : ℤ) : ℝ) ∂μ) = 0 := hentry.mean_zero
    refine hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero (a := -|(w j : ℝ)|) (b := |(w j : ℝ)|)
      (hentry.aemeasurable.mul_const _) ?_ ?_
    · filter_upwards [hentry.mem] with ω he
      have hc1 : |((J ω i j : ℤ) : ℝ)| ≤ 1 := by
        rcases he with h | h | h <;> rw [h] <;> norm_num
      have hbound : |((J ω i j : ℤ) : ℝ) * (w j : ℝ)| ≤ |(w j : ℝ)| := by
        rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) hc1
      exact Set.mem_Icc.mpr (abs_le.mp hbound)
    · rw [integral_mul_const, hmz, zero_mul]
  -- (3) Sum over the row.
  have hsum := HasSubgaussianMGF.sum_of_iIndepFun hXindep hsubG
  -- (4) Reconcile the function and the sub-Gaussian parameter.
  have hfun : rowInner J w i = fun ω => ∑ j : Fin m, ((J ω i j : ℤ) : ℝ) * (w j : ℝ) := by
    funext ω
    simp only [rowInner, proj, Matrix.mulVec, dotProduct]
    push_cast
    rfl
  have hc : (∑ j : Fin m, (‖|(w j : ℝ)| - -|(w j : ℝ)|‖₊ / 2) ^ 2) = (sqNorm w).toNNReal := by
    apply NNReal.coe_injective
    rw [NNReal.coe_sum, Real.coe_toNNReal _ (sqNorm_nonneg w), sqNorm]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    rw [Real.norm_eq_abs, show |(w j : ℝ)| - -|(w j : ℝ)| = 2 * |(w j : ℝ)| by ring,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 * |(w j : ℝ)|),
      mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), sq_abs]
  rw [hfun, ← hc]
  exact hsum

/-- **N1 (Lemma 5, inequality I — the easy half).** For any `κ ∈ (0,1)` and modulus `q` there are
parameters `(n, α, β)` so that for every width `m`, every χ-matrix `J` of height `n`, and every
nonzero `w`, the squared-norm ratio `‖Jw‖²/‖w‖²` lands in `[α, β]` except with probability `κ`.
Concretely (BS23 Lemma 4.1, `κ = 2⁻¹²⁸`): `n = 256`, `[α, β] = [30, 337]`.

Reachable in *shape* now via Hoeffding-for-sums on `‖Jw‖₂² = ∑ⱼ ⟨rⱼ,w⟩²` (loose constants); the
tight `[√30,√337]` needs sub-exponential Bernstein or `JL.Analytic.ChiSquaredTailHyp` (Gaussian
model). Part (I) carries no modulus, so this `Prop` (unlike `Lemma5_ModqSoundness`) is `q`-free. -/
def Lemma5_NormPreservation (κ : ℝ) : Prop :=
  ∃ P : Params, 0 < P.α ∧ P.α ≤ P.β ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ}
      (J : Ω → Matrix (Fin P.n) (Fin m) ℤ), IsChiMatrix J μ → ∀ w : Fin m → ℤ, w ≠ 0 →
        μ.real {ω | normRatio J w ω ∉ Set.Icc P.α P.β} ≤ κ

/-- **N2 (Lemma 5, inequality II — the hard half).** With the same parameters as N1, for a *norm*
threshold `0 < θ ≤ q/b` and any `w ∈ [±q/2]^m` with `‖w‖₂ ≥ θ`, the reduced projection norm
`‖Jw mod q‖₂` exceeds `α·θ` except with probability `κ`: wrap-around mod `q` cannot make a long
vector look short. (`θ` is an ℓ₂-norm threshold, matching BS23 Lemma 4.2's `‖w‖₂ ≥ b`,
`‖Πw mod q‖₂ < √30·b` — *not* a squared threshold.)

Proof (BS23 App A) splits on `w`'s geometry — Case 1 (`‖w‖₂<q/10`, → N1), Case 2 (`‖w‖∞≥q/60`,
Chernoff), **Case 3 (`‖w‖₂≥q/10 ∧ ‖w‖∞<q/60`, needs `JL.Analytic.BerryEsseenHyp`)**. The eventual
`theorem` discharging this will take `(hBE : BerryEsseenHyp)`. -/
def Lemma5_ModqSoundness (κ : ℝ) (q : ℕ) : Prop :=
  ∃ P : Params, 0 < P.α ∧ P.α ≤ P.β ∧ 0 < P.b ∧
    ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ}
      (J : Ω → Matrix (Fin P.n) (Fin m) ℤ), IsChiMatrix J μ →
        ∀ (w : Fin m → ℤ) (θ : ℝ), 0 < θ → θ ≤ q / P.b →
          (∀ j, (w j : ℝ) ∈ Set.Icc (-(q : ℝ) / 2) ((q : ℝ) / 2)) → θ ≤ l2Norm w →
            μ.real {ω | projModL2Norm J w q ω ≤ P.α * θ} ≤ κ

/-- **N3 (Lemma 6).** Block-diagonal extension `V = (I ⊗ J)·W`: the per-block N1 guarantee lifts to
a multi-column witness at the cost of a union-bound factor `κ·r·blocks`. Stated as the conditional
"per-block window bound ⟹ union-bounded bound" so its proof depends only on the *statement* of N1.

Reachable now: pure structural bookkeeping + `MeasureTheory.measure_biUnion_le`. On the critical
path to a *usable* conjecture (it is the structured form the RoKoko protocol consumes), and its
union factor `r·blocks` (`= r·m_w/m_rp` in the paper) feeds the asymptotic scaling: end-to-end
failure `κ` needs per-block `κ/(r·blocks)`, i.e. `n_rp = Θ(log(1/κ) + log(r·m_w/m_rp))`. -/
def Lemma6_Structured (κ : ℝ) (P : Params) : Prop :=
  (∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m : ℕ}
    (J : Ω → Matrix (Fin P.n) (Fin m) ℤ), IsChiMatrix J μ → ∀ w : Fin m → ℤ, w ≠ 0 →
      μ.real {ω | normRatio J w ω ∉ Set.Icc P.α P.β} ≤ κ) →
  ∀ {Ω : Type} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {m r blocks : ℕ}
    (J : Ω → Matrix (Fin P.n) (Fin m) ℤ), IsChiMatrix J μ →
    ∀ (W : Fin r → Fin blocks → Fin m → ℤ), (∀ c i, W c i ≠ 0) →
      μ.real {ω | ∃ c i, normRatio J (W c i) ω ∉ Set.Icc P.α P.β} ≤ κ * r * blocks

/-- **N3 proved** (PROVEN — the union-bound half of Lemma 6). The per-column/per-block reduction is
the structural core; the Pythagorean `‖vⱼ‖₂² = ∑ᵢ ‖vⱼ,ᵢ‖₂²` concatenation step (combining the
per-block windows into a single per-column window) is deferred to the full matrix version. -/
theorem lemma6_structured (κ : ℝ) (P : Params) : Lemma6_Structured κ P := by
  intro hnorm Ω _ μ _ m r blocks J hJ W hW
  -- The "some (column, block) is bad" event is the union over the product index of per-pair events.
  have hset : {ω | ∃ c i, normRatio J (W c i) ω ∉ Set.Icc P.α P.β}
      = ⋃ p : Fin r × Fin blocks, {ω | normRatio J (W p.1 p.2) ω ∉ Set.Icc P.α P.β} := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iUnion, Prod.exists]
  rw [hset]
  calc
    μ.real (⋃ p : Fin r × Fin blocks, {ω | normRatio J (W p.1 p.2) ω ∉ Set.Icc P.α P.β})
        ≤ ∑ p : Fin r × Fin blocks, μ.real {ω | normRatio J (W p.1 p.2) ω ∉ Set.Icc P.α P.β} :=
      measureReal_iUnion_fintype_le _
    _ ≤ ∑ _p : Fin r × Fin blocks, κ :=
      Finset.sum_le_sum fun p _ => hnorm μ J hJ (W p.1 p.2) (hW p.1 p.2)
    _ = κ * r * blocks := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin,
        nsmul_eq_mul, Nat.cast_mul]
      ring

end JL
