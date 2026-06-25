/-
Copyright (c) 2026. Released under Apache 2.0 license.
JL-lean: formal verification of the lattice Johnson–Lindenstrauss projection lemmas.
-/
import JL.RoKoko
import JL.Analytic.BerryEsseen

/-!
# BS23 Lemma 4.2, Case 3 — the Berry–Esseen anti-concentration case

**Stability: in progress.** This file discharges `JL.Case3Hyp` (the irreducible geometric case of
mod-`q` soundness) *modulo* its two standard analytic inputs, both taken as explicit hypotheses:

* `JL.Analytic.BerryEsseenHyp` — the quantitative CLT (the project's irreducible gap); and
* a **Gaussian small-ball / interval-mass** estimate (also absent from Mathlib, and *not* derivable
  from Berry–Esseen — see `mathlib-audit`), isolated here as `GaussianSmallBallHyp`.

The proof is layered (see `JL/doc/paper-to-lean-map.md`):

1. **Structural reduction (no analytic input).** `{‖Jw mod q‖₂ ≤ α·θ} ⊆ ⋂ᵢ Bᵢ` where
   `Bᵢ = {|centeredMod q ⟨rᵢ,w⟩| ≤ α·θ}` — a small ℓ₂ norm forces *every* coordinate small.
2. **Product over independent rows.** `μ(⋂ᵢ Bᵢ) ≤ pⁿ` from a per-row bound `μ(Bᵢ) ≤ p` and the
   independence of the `n` rows of `J` (built by hand; Mathlib has no block-grouping lemma).
3. **Per-row anti-concentration.** `μ(Bᵢ) ≤ p`: `⟨rᵢ,w⟩` is a sum of independent small terms with
   variance `½‖w‖₂²`; Berry–Esseen + the Gaussian small-ball bound give `p = 0.39 + 2·0.15 < 1`.

This file currently builds layer 1. Layers 2–3 are added incrementally (commit-by-commit).
-/

open MeasureTheory ProbabilityTheory Matrix
open scoped NNReal

namespace JL

-- Case 3's downstream targets (`Case3Hyp`, `AntiConcentrationInterface`) and the N0 leaf are all
-- stated at `Type` (Type 0); we match that here so the pieces compose without universe friction.
variable {Ω : Type} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-! ### Layer 1a — a small ℓ₂ norm forces every coordinate small -/

/-- If the ℓ₂ norm of an integer vector is `≤ c` (`c ≥ 0`), then each coordinate is `≤ c` in
absolute value. (`(uᵢ)² ≤ ∑ⱼ (uⱼ)² = ‖u‖₂² ≤ c²`, then take square roots.) -/
theorem abs_coord_le_of_l2Norm_le {k : ℕ} {u : Fin k → ℤ} {c : ℝ} (hc : 0 ≤ c)
    (h : l2Norm u ≤ c) (i : Fin k) : |(u i : ℝ)| ≤ c := by
  have hsq : (u i : ℝ) ^ 2 ≤ c ^ 2 := by
    calc (u i : ℝ) ^ 2
        ≤ sqNorm u := by
          simp only [sqNorm]
          exact Finset.single_le_sum (f := fun j => ((u j : ℝ)) ^ 2)
            (fun j _ => sq_nonneg _) (Finset.mem_univ i)
      _ = l2Norm u ^ 2 := (l2Norm_sq u).symm
      _ ≤ c ^ 2 := by nlinarith [l2Norm_nonneg u, h, hc]
  rw [← Real.sqrt_sq_eq_abs]
  calc Real.sqrt ((u i : ℝ) ^ 2) ≤ Real.sqrt (c ^ 2) := Real.sqrt_le_sqrt hsq
    _ = c := Real.sqrt_sq hc

/-- **Layer 1a (structural inclusion, no analytic input).** The event "the reduced projection is
short" (`‖Jw mod q‖₂ ≤ c`, `c ≥ 0`) is contained in the intersection over rows of the per-row
events "this coordinate of `Jw mod q` is short". This is the step that converts an ℓ₂ bound into the
`n` coordinatewise (per-row) bounds that Berry–Esseen will control. -/
theorem projMod_short_subset_iInter {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ) (w : Fin m → ℤ)
    (q : ℕ) {c : ℝ} (hc : 0 ≤ c) :
    {ω | projModL2Norm J w q ω ≤ c}
      ⊆ ⋂ i, {ω | |(centeredMod q ((proj J w) ω i) : ℝ)| ≤ c} := by
  intro ω hω
  simp only [Set.mem_setOf_eq, projModL2Norm] at hω
  simp only [Set.mem_iInter, Set.mem_setOf_eq]
  intro i
  exact abs_coord_le_of_l2Norm_le hc hω i

/-! ### Layer 1b — independent rows give a product bound `≤ pⁿ`

The `i`-th projected coordinate `(Jw)ᵢ = ⟨rᵢ, w⟩` depends only on row `i` of `J`. Since the rows are
independent, the per-row "short" events are independent, so the probability that *all* `n` of them
are short is `≤ pⁿ`. The independence of the rows is the structural premise `hRowIndep` below:
**this is provable infrastructure** (block-independence of a product-indexed `iIndepFun` family —
absent from Mathlib v4.31.0, see `mathlib-audit`), *not* an analytic gap. It is isolated here as an
explicit hypothesis so the downstream Berry–Esseen layers compose against a machine-checked product
bound; discharging it is a separate (purely measure-theoretic) task. -/

/-- The integer-valued `i`-th projected coordinate `(Jw)ᵢ = ⟨rᵢ, w⟩ : Ω → ℤ`. A function of row `i`
of `J` only; the rows being independent makes the family `i ↦ projCoord J w i` independent. -/
def projCoord {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ) (w : Fin m → ℤ) (i : Fin n) : Ω → ℤ :=
  fun ω => (proj J w) ω i

/-- **Layer 1b (product over independent rows).** If the projected coordinates `i ↦ projCoord J w i`
are independent (`hRowIndep` — provable structural infrastructure) and each lands in a fixed
measurable target `T i` with probability `≤ p`, then *all* of them do so with probability `≤ pⁿ`. -/
theorem iInter_row_prob_le {n m : ℕ} [IsProbabilityMeasure μ] (J : Ω → Matrix (Fin n) (Fin m) ℤ)
    (w : Fin m → ℤ) {p : ℝ}
    (hRowIndep : iIndepFun (fun i : Fin n => projCoord J w i) μ)
    {T : Fin n → Set ℤ} (hT : ∀ i, MeasurableSet (T i))
    (hper : ∀ i, μ.real {ω | projCoord J w i ω ∈ T i} ≤ p) :
    μ.real {ω | ∀ i, projCoord J w i ω ∈ T i} ≤ p ^ n := by
  classical
  -- The "all rows in target" event is the intersection of the per-row preimages.
  have hset : {ω | ∀ i, projCoord J w i ω ∈ T i} = ⋂ i, projCoord J w i ⁻¹' T i := by
    ext ω; simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage]
  -- Each preimage is measurable w.r.t. the comap of its own row coordinate.
  have hmeas : ∀ i, MeasurableSet[(inferInstance : MeasurableSpace ℤ).comap (projCoord J w i)]
      (projCoord J w i ⁻¹' T i) := fun i => ⟨T i, hT i, rfl⟩
  -- Independence turns the measure of the intersection into the product of the per-row measures.
  have hprod : μ (⋂ i, projCoord J w i ⁻¹' T i) = ∏ i, μ (projCoord J w i ⁻¹' T i) :=
    hRowIndep.meas_iInter hmeas
  rw [hset, measureReal_def, hprod, ENNReal.toReal_prod]
  calc ∏ i, (μ (projCoord J w i ⁻¹' T i)).toReal
      ≤ ∏ _i : Fin n, p :=
        Finset.prod_le_prod (fun i _ => ENNReal.toReal_nonneg) (fun i _ => hper i)
    _ = p ^ n := by simp [Finset.prod_const]

/-- **Layers 1a+1b combined (the structural core of Case 3, no analytic input).** Given row
independence (`hRowIndep`, provable infrastructure) and a per-row anti-concentration bound `≤ p`
(the Berry–Esseen consequence, supplied by Layers 2–3), the probability that the reduced projection
is short (`‖Jw mod q‖₂ ≤ c`, `c ≥ 0`) is `≤ pⁿ`. This is exactly the `pⁿ` shape of
`AntiConcentrationInterface`, with the per-row bound `p` and row independence as the only inputs. -/
theorem projMod_short_prob_le {n m : ℕ} [IsProbabilityMeasure μ]
    (J : Ω → Matrix (Fin n) (Fin m) ℤ) (w : Fin m → ℤ) (q : ℕ) {c p : ℝ} (hc : 0 ≤ c)
    (hRowIndep : iIndepFun (fun i : Fin n => projCoord J w i) μ)
    (hper : ∀ i, μ.real {ω | |(centeredMod q ((proj J w) ω i) : ℝ)| ≤ c} ≤ p) :
    μ.real {ω | projModL2Norm J w q ω ≤ c} ≤ p ^ n := by
  have key : μ.real {ω | ∀ i, projCoord J w i ω ∈ {x : ℤ | |(centeredMod q x : ℝ)| ≤ c}} ≤ p ^ n :=
    iInter_row_prob_le J w hRowIndep (fun _ => MeasurableSet.of_discrete) hper
  refine le_trans (measureReal_mono ?_) key
  intro ω hω
  have hmem := projMod_short_subset_iInter J w q hc hω
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hmem ⊢
  exact hmem

/-! ### Layer 2 — χ-moments (the data Berry–Esseen consumes)

For Berry–Esseen we feed it the summands `Xⱼ = χⱼ·wⱼ` of a row inner product. The three moment facts
below come straight from `IsChiEntry` (`χ` valued in `{-1,0,1}`, mean `0`, `E[χ²]=½`). The key
non-obvious one is the third absolute moment: since `|χ|∈{0,1}` we have `|χ|³=χ²`, so `E|χ|³=½` too;
hence the per-summand Lyapunov ratio `ρⱼ/σⱼ² = (½|wⱼ|³)/(½wⱼ²) = |wⱼ|`, giving `L = ‖w‖∞`. -/

/-- `E|χ|³ = ½`: on the support `{-1,0,1}` we have `|χ|³ = χ²`, so the third absolute moment equals
the second moment. -/
theorem IsChiEntry.thirdMoment {X : Ω → ℝ} (h : IsChiEntry X μ) : ∫ ω, |X ω| ^ 3 ∂μ = 1 / 2 := by
  rw [← h.snd_moment]
  apply integral_congr_ae
  filter_upwards [h.mem] with ω hω
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hω
  rcases hω with h1 | h1 | h1 <;> rw [h1] <;> norm_num

/-- A scaled χ entry `ω ↦ χ·c` has mean `0`. -/
theorem IsChiEntry.scaled_mean {X : Ω → ℝ} (h : IsChiEntry X μ) (c : ℝ) :
    ∫ ω, X ω * c ∂μ = 0 := by
  rw [integral_mul_const, h.mean_zero, zero_mul]

/-- A scaled χ entry `ω ↦ χ·c` has second moment `½c²` (so variance `½c²`, mean being `0`). -/
theorem IsChiEntry.scaled_sndMoment {X : Ω → ℝ} (h : IsChiEntry X μ) (c : ℝ) :
    ∫ ω, (X ω * c) ^ 2 ∂μ = (1 / 2) * c ^ 2 := by
  simp only [mul_pow]
  rw [integral_mul_const, h.snd_moment]

/-- A scaled χ entry `ω ↦ χ·c` has third absolute moment `½|c|³`. -/
theorem IsChiEntry.scaled_thirdMoment {X : Ω → ℝ} (h : IsChiEntry X μ) (c : ℝ) :
    ∫ ω, |X ω * c| ^ 3 ∂μ = (1 / 2) * |c| ^ 3 := by
  simp only [abs_mul, mul_pow]
  rw [integral_mul_const, h.thirdMoment]

/-! ### Layer 2b — the wrap-around tail (from N0, sub-Gaussian)

The mod-`q` wrap-around (all lattice intervals except the one nearest the mean) lies in the far tail
`{|⟨rᵢ,w⟩| ≥ q/2 − c}`. Berry–Esseen is the *wrong* tool there (its uniform error `≈0.15` dwarfs the
actual mass); the right tool is the genuine sub-Gaussian tail of the row inner product, i.e. N0. This
is why N0 is the leaf of the DAG — it controls the wrap, so only ONE Berry–Esseen application (the
central interval) is needed and the per-row bound stays `0.39 + 2·0.15 < 1`. -/

/-- Two-sided sub-Gaussian (Chernoff) tail: `Pr[|X| ≥ ε] ≤ 2 e^{−ε²/(2c)}`. -/
theorem measureReal_abs_ge_le [IsFiniteMeasure μ] {X : Ω → ℝ} {c : ℝ≥0}
    (h : HasSubgaussianMGF X c μ) {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |X ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * c)) := by
  have h1 := h.measure_ge_le hε
  have h2 := h.neg.measure_ge_le hε
  have hsub : {ω | ε ≤ |X ω|} ⊆ {ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rcases le_abs.mp hω with h' | h'
    · exact Or.inl h'
    · exact Or.inr h'
  calc μ.real {ω | ε ≤ |X ω|}
      ≤ μ.real ({ω | ε ≤ X ω} ∪ {ω | ε ≤ -X ω}) := measureReal_mono hsub
    _ ≤ μ.real {ω | ε ≤ X ω} + μ.real {ω | ε ≤ -X ω} := measureReal_union_le _ _
    _ ≤ Real.exp (-ε ^ 2 / (2 * c)) + Real.exp (-ε ^ 2 / (2 * c)) := add_le_add h1 h2
    _ = 2 * Real.exp (-ε ^ 2 / (2 * c)) := by ring

/-- **Wrap-around tail of a row inner product** (specialisation of `measureReal_abs_ge_le` via N0).
The probability that `⟨rᵢ,w⟩` is at least `ε` in absolute value is `≤ 2 e^{−ε²/(2‖w‖₂²)}`. -/
theorem rowInner_abs_ge_le [IsProbabilityMeasure μ] {n m : ℕ}
    (J : Ω → Matrix (Fin n) (Fin m) ℤ) (hJ : IsChiMatrix J μ) (w : Fin m → ℤ) (i : Fin n)
    {ε : ℝ} (hε : 0 ≤ ε) :
    μ.real {ω | ε ≤ |rowInner J w i ω|} ≤ 2 * Real.exp (-ε ^ 2 / (2 * sqNorm w)) := by
  have h := measureReal_abs_ge_le (n0_rowSubgaussian μ J hJ w i) hε
  rwa [Real.coe_toNNReal _ (sqNorm_nonneg w)] at h

end JL
