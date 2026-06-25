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

/-! ### Layer 2c — the center/wrap dichotomy (pure `Int.bmod` geometry)

A small balanced residue `x mod q` forces *either* no wrap (`|x| ≤ c`, handled by Berry–Esseen on the
single central interval) *or* a full wrap (`|x| ≥ q − c`, handled by the sub-Gaussian tail). This is
the integer fact behind RoKoko's `0.39 + 2·0.15`: only one central interval needs Berry–Esseen. -/

/-- **Center/wrap dichotomy.** If the balanced residue of `x` mod `q` is at most `c` in absolute
value, then `x` itself is either within `c` of `0` (no wrap) or at least `q − c` from `0` (wrapped). -/
theorem abs_le_or_ge_of_centeredMod_le {q : ℕ} {x : ℤ} {c : ℝ}
    (h : |(centeredMod q x : ℝ)| ≤ c) : |(x : ℝ)| ≤ c ∨ (q : ℝ) - c ≤ |(x : ℝ)| := by
  simp only [centeredMod] at h
  have hz : x = Int.bmod x q + (q : ℤ) * Int.bdiv x q := by
    rw [Int.bmod_eq_self_sub_mul_bdiv]; ring
  have hdecomp : (x : ℝ) = (Int.bmod x q : ℝ) + (q : ℝ) * (Int.bdiv x q : ℝ) := by
    exact_mod_cast hz
  rcases eq_or_ne (Int.bdiv x q) 0 with hk0 | hk0
  · left
    have hx : (x : ℝ) = (Int.bmod x q : ℝ) := by rw [hdecomp, hk0]; push_cast; ring
    rw [hx]; exact h
  · right
    have hk1 : (1 : ℝ) ≤ |(Int.bdiv x q : ℝ)| := by
      have h1 : (1 : ℤ) ≤ |Int.bdiv x q| := Int.one_le_abs hk0
      calc (1 : ℝ) ≤ ((|Int.bdiv x q| : ℤ) : ℝ) := by exact_mod_cast h1
        _ = |(Int.bdiv x q : ℝ)| := by rw [Int.cast_abs]
    have hq : (0 : ℝ) ≤ (q : ℝ) := by positivity
    have hrev : |(q : ℝ) * (Int.bdiv x q : ℝ)| - |(Int.bmod x q : ℝ)| ≤ |(x : ℝ)| := by
      have ht := abs_sub_abs_le_abs_sub ((q : ℝ) * (Int.bdiv x q : ℝ)) (-(Int.bmod x q : ℝ))
      rw [abs_neg] at ht
      have e : (q : ℝ) * (Int.bdiv x q : ℝ) - -(Int.bmod x q : ℝ) = (x : ℝ) := by
        rw [hdecomp]; ring
      rwa [e] at ht
    have habs : |(q : ℝ) * (Int.bdiv x q : ℝ)| = (q : ℝ) * |(Int.bdiv x q : ℝ)| := by
      rw [abs_mul, abs_of_nonneg hq]
    nlinarith [hk1, hq, hrev, habs, h, mul_le_mul_of_nonneg_left hk1 hq]

/-- **Measure-level center/wrap split.** The per-row bad event splits (by the dichotomy above) into
the central interval `{|⟨rᵢ,w⟩| ≤ c}` and the wrap-around tail `{q − c ≤ |⟨rᵢ,w⟩|}`. The first is
bounded by Berry–Esseen + the Gaussian small-ball; the second by the sub-Gaussian tail
(`rowInner_abs_ge_le`). -/
theorem perRow_split [IsProbabilityMeasure μ] {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ)
    (w : Fin m → ℤ) (q : ℕ) (i : Fin n) {c : ℝ} :
    μ.real {ω | |(centeredMod q ((proj J w) ω i) : ℝ)| ≤ c}
      ≤ μ.real {ω | |rowInner J w i ω| ≤ c}
        + μ.real {ω | (q : ℝ) - c ≤ |rowInner J w i ω|} := by
  have hsub : {ω | |(centeredMod q ((proj J w) ω i) : ℝ)| ≤ c}
      ⊆ {ω | |rowInner J w i ω| ≤ c} ∪ {ω | (q : ℝ) - c ≤ |rowInner J w i ω|} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    rcases abs_le_or_ge_of_centeredMod_le hω with h | h
    · exact Or.inl h
    · exact Or.inr h
  exact (measureReal_mono hsub).trans (measureReal_union_le _ _)

/-! ### Layer 2d — the central interval (the single Berry–Esseen application)

Berry–Esseen transfers the central-interval probability of `S = ⟨rᵢ,w⟩` to the matching Gaussian at
the cost of `2δ` (two CDF evaluations), where the Gaussian mass is bounded by the small-ball `p₀`.
The integer/atom boundary is sidestepped by using the strictly-lower cut `{S ≤ −c−1}`: a point with
`|S| ≤ c` has `S > −c−1`, so it survives the set difference, and no atom term appears. -/

/-- **Central-interval Berry–Esseen transfer.** If the CDF of `S` is `δ`-close to that of `N(0,v)`
(Berry–Esseen) and the Gaussian puts mass `≤ p₀` on `[−c−1, c]` (small-ball), then
`Pr[|S| ≤ c] ≤ p₀ + 2δ`. This is the lone Berry–Esseen application of Case 3. -/
theorem central_interval_le [IsProbabilityMeasure μ] {S : Ω → ℝ} (hSae : AEMeasurable S μ)
    {v : NNReal} {c δ p₀ : ℝ} (hc : 0 ≤ c)
    (hbe : ∀ x : ℝ, |μ.real {ω | S ω ≤ x} - (gaussianReal 0 v).real (Set.Iic x)| ≤ δ)
    (hsb : (gaussianReal 0 v).real (Set.Icc (-c - 1) c) ≤ p₀) :
    μ.real {ω | |S ω| ≤ c} ≤ p₀ + 2 * δ := by
  have hsub : {ω | |S ω| ≤ c} ⊆ {ω | S ω ≤ c} \ {ω | S ω ≤ -c - 1} := by
    intro ω hω
    simp only [Set.mem_setOf_eq] at hω
    refine ⟨(abs_le.mp hω).2, ?_⟩
    intro hB
    simp only [Set.mem_setOf_eq] at hB
    linarith [(abs_le.mp hω).1]
  have hBA : {ω | S ω ≤ -c - 1} ⊆ {ω | S ω ≤ c} := by
    intro ω hω; simp only [Set.mem_setOf_eq] at *; linarith [hc]
  -- `{S ≤ -c-1}` is null-measurable (preimage of `Iic` under the a.e.-measurable `S`), enough for
  -- the set-difference measure identity below.
  have hnull : NullMeasurableSet {ω | S ω ≤ -c - 1} μ :=
    hSae.nullMeasurableSet_preimage measurableSet_Iic
  have hdiff : μ.real ({ω | S ω ≤ c} \ {ω | S ω ≤ -c - 1})
      = μ.real {ω | S ω ≤ c} - μ.real {ω | S ω ≤ -c - 1} := by
    have key := measureReal_inter_add_sdiff₀ (s := {ω | S ω ≤ c}) hnull
    rw [Set.inter_eq_right.mpr hBA] at key
    linarith [key]
  have hcov : (gaussianReal 0 v).real (Set.Iic c)
      ≤ (gaussianReal 0 v).real (Set.Iic (-c - 1))
        + (gaussianReal 0 v).real (Set.Icc (-c - 1) c) := by
    have hc' : Set.Iic c ⊆ Set.Iic (-c - 1) ∪ Set.Icc (-c - 1) c := by
      intro x hx
      simp only [Set.mem_Iic] at hx
      by_cases hxle : x ≤ -c - 1
      · exact Or.inl hxle
      · exact Or.inr ⟨(not_le.mp hxle).le, hx⟩
    exact (measureReal_mono hc').trans (measureReal_union_le _ _)
  have hbe1 := abs_le.mp (hbe c)
  have hbe2 := abs_le.mp (hbe (-c - 1))
  calc μ.real {ω | |S ω| ≤ c}
      ≤ μ.real ({ω | S ω ≤ c} \ {ω | S ω ≤ -c - 1}) := measureReal_mono hsub
    _ = μ.real {ω | S ω ≤ c} - μ.real {ω | S ω ≤ -c - 1} := hdiff
    _ ≤ p₀ + 2 * δ := by linarith [hbe1.1, hbe1.2, hbe2.1, hbe2.2, hcov, hsb]

/-- The row inner product `⟨rᵢ,w⟩ = ∑ⱼ rᵢⱼwⱼ` is a.e.-measurable (a finite sum of scaled
a.e.-measurable χ entries). -/
theorem IsChiMatrix.aemeasurable_rowInner {n m : ℕ} {J : Ω → Matrix (Fin n) (Fin m) ℤ}
    (hJ : IsChiMatrix J μ) (w : Fin m → ℤ) (i : Fin n) : AEMeasurable (rowInner J w i) μ := by
  have hfun : rowInner J w i = ∑ j : Fin m, (fun ω => ((J ω i j : ℤ) : ℝ) * (w j : ℝ)) := by
    funext ω
    simp only [rowInner, proj, Matrix.mulVec, dotProduct, Finset.sum_apply]
    push_cast; rfl
  rw [hfun]
  exact Finset.aemeasurable_sum _ fun j _ => ((hJ.entry (i, j)).aemeasurable).mul_const _

/-! ### Layer 2 assembly — the per-row bound

Combining the center/wrap split with the central Berry–Esseen transfer and the sub-Gaussian wrap
tail yields the per-row bad probability `≤ (p₀ + 2δ) + 2e^{−(q−c)²/(2‖w‖₂²)}`. In Case 3, after the
sub-vector reduction (which forces `‖w‖₂ < q/10` so the wrap term is negligible and `v` lands in the
small-ball window), this is RoKoko's `0.39 + 2·0.15 + tiny < 1`. -/

/-- **The per-row bound (PROVEN, taking the Berry–Esseen output and the small-ball as inputs).**
For one row, the bad event `‖⟨rᵢ,w⟩ mod q‖ ≤ c` has probability `≤ (p₀ + 2δ) + 2e^{−(q−c)²/(2‖w‖₂²)}`:
the central interval contributes `p₀ + 2δ` (`central_interval_le`, the lone Berry–Esseen application)
and the wrap-around `2e^{−(q−c)²/(2‖w‖₂²)}` (`rowInner_abs_ge_le`, the sub-Gaussian tail from N0). -/
theorem perRow_bound [IsProbabilityMeasure μ] {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ)
    (hJ : IsChiMatrix J μ) (w : Fin m → ℤ) (i : Fin n) (q : ℕ) {c δ p₀ : ℝ} {v : NNReal}
    (hc : 0 ≤ c) (hcq : c ≤ q)
    (hbe : ∀ x : ℝ,
      |μ.real {ω | rowInner J w i ω ≤ x} - (gaussianReal 0 v).real (Set.Iic x)| ≤ δ)
    (hsb : (gaussianReal 0 v).real (Set.Icc (-c - 1) c) ≤ p₀) :
    μ.real {ω | |(centeredMod q ((proj J w) ω i) : ℝ)| ≤ c}
      ≤ (p₀ + 2 * δ) + 2 * Real.exp (-((q : ℝ) - c) ^ 2 / (2 * sqNorm w)) := by
  have hcentral := central_interval_le (hJ.aemeasurable_rowInner w i) hc hbe hsb
  have hwrap := rowInner_abs_ge_le J hJ w i (ε := (q : ℝ) - c) (by linarith)
  exact (perRow_split J w q i).trans (add_le_add hcentral hwrap)

/-! ### Layer 3 — the constant chase (`p = 0.39 + 2·0.15 < 1`)

The per-row bound is `p = (p₀ + 2δ) + wrap`. The question RoKoko hedges on is whether, in the Case-3
regime, the *constants* satisfy `p < 1` uniformly. They do, with comfortable margin — and the
load-bearing piece (the Berry–Esseen slack `δ`, the only one tied to the sharp Esseen constant) is
pure arithmetic, verified below. -/

/-- **The Berry–Esseen slack in Case 3 is `< 0.146`.** With the sharp Esseen constant
`esseenConst = 0.56` (Korolev–Shevtsova) and the regime ratio `L/√v ≤ (q/60)/(q/(11√2)) = 11√2/60`,
the per-CDF Berry–Esseen error `δ = esseenConst·L/√v` is below `0.146` — RoKoko's `0.15`. This is the
single constant tied to Berry–Esseen, and it is fully machine-checked. -/
theorem case3_delta_bound : Analytic.esseenConst * (11 * Real.sqrt 2 / 60) < 0.146 := by
  have h2 : Real.sqrt 2 < 1.4143 := by
    have : (2 : ℝ) < 1.4143 ^ 2 := by norm_num
    exact (Real.sqrt_lt' (by norm_num)).mpr this
  have hnn : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  simp only [Analytic.esseenConst]
  nlinarith [h2, hnn]

/-- **The per-row budget closes below `1`.** With the small-ball `p₀ ≤ 0.40` (the central interval),
the Berry–Esseen slack `δ ≤ 0.146` (`case3_delta_bound`), and the sub-Gaussian wrap `≤ 0.001`
(in fact `≈ 10⁻²⁰`), the per-row bad probability `p = (p₀ + 2δ) + wrap ≤ 0.693 < 1`. So the constant
coordination RoKoko hedges on does close — with margin `≈ 0.31`. -/
theorem case3_budget_closes {p₀ δ wrap : ℝ}
    (hp0 : p₀ ≤ 0.40) (hδ : δ ≤ 0.146) (hwrap : wrap ≤ 0.001) :
    (p₀ + 2 * δ) + wrap < 1 := by linarith

/-- **The small-ball headroom (the margin, quantified).** The budget still closes for *any* small-ball
constant `p₀ ≤ 0.70`, not just the realised `≈ 0.40`. Since `p₀ = 2Φ(c/σ)−1` increases with the
shortness ratio `c/σ ≈ (α/b)·11√2`, this headroom is spendable: it lets the soundness ratio `α/b`
roughly double (`1/30 → ~1/15`) while keeping the per-row bad probability `< 1`. The margin is thus a
parameter **trade-off frontier** (soundness ratio vs. row count `n_rp = log(1/κ)/log(1/p)`), not free
improvement. -/
theorem case3_budget_frontier {p₀ δ wrap : ℝ}
    (hp0 : p₀ ≤ 0.70) (hδ : δ ≤ 0.146) (hwrap : wrap ≤ 0.001) :
    (p₀ + 2 * δ) + wrap < 1 := by linarith

end JL
