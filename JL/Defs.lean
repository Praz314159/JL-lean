/-
Copyright (c) 2026. Released under Apache 2.0 license.
JL-lean: formal verification of the lattice Johnson–Lindenstrauss projection lemmas.
-/
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Matrix.Mul

/-!
# Core definitions for the ring Johnson–Lindenstrauss lemmas

This file fixes the probability model and the basic geometric quantities used throughout the
JL development (see `JL/doc/paper-to-lean-map.md` for the lemma DAG and `JL/doc/mathlib-audit.md`
for the Mathlib coverage).

Design choices (per project kickoff):
* **Abstract probability model.** The projection matrix `J` is an arbitrary measurable map
  `Ω → Matrix (Fin n) (Fin m) ℤ` on a generic probability space, whose entries are required to be
  independent (`iIndepFun`) and each distributed as the JL source distribution `χ`
  (`IsChiEntry`). This matches Mathlib's `ProbabilityTheory.HasSubgaussianMGF` API for maximal
  reuse, while a concrete `χ` can be supplied later as one instance of `IsChiEntry`.
* **Integer entries, real norms.** `J` and the witness `w` are integer-valued (χ is supported on
  `{-1,0,1}` and `w ∈ ℤ^m`); norms are computed in `ℝ` via casts. This keeps the `mod q` reduction
  (centered/balanced representative) and the sub-Gaussian analysis on the same objects.
* **Norm-form public, squared internal.** RoKoko Lemma 5/6 state every bound on the **ℓ₂ norm**
  `‖·‖₂` (e.g. `‖Jw‖₂/‖w‖₂ ∈ [αrp, βrp] = [√30, √337]`), *not* the squared norm — there is no typo;
  the paper's `‖·‖₂` is the ℓ₂ subscript. We therefore expose statements in `l2Norm` form
  (faithful to the paper and to the conjecture's `Θ(√log)` scaling) and use `sqNorm` only as an
  internal proof tool, bridged by `l2Norm_sq : l2Norm v ^ 2 = sqNorm v`. The paper's own Lemma 6
  proof does exactly this (states `‖·‖₂`, squares for the Pythagorean concatenation step).
-/

open MeasureTheory ProbabilityTheory Matrix

namespace JL

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}

/-- The Johnson–Lindenstrauss source distribution `χ`, as a predicate on a single real-valued
random variable `X`. It records the defining properties of `χ` on `{-1,0,1}`
(`Pr[0]=1/2`, `Pr[±1]=1/4`): a.s. valued in `{-1,0,1}`, mean `0`, and second moment `1/2`.
These are exactly the moments used in RoKoko Appendix A (`E[⟨r,w⟩²] = ½‖w‖²`). -/
structure IsChiEntry (X : Ω → ℝ) (μ : Measure Ω) : Prop where
  /-- `X` is (a.e.) measurable. -/
  aemeasurable : AEMeasurable X μ
  /-- `X` is almost surely valued in the support `{-1, 0, 1}`. -/
  mem : ∀ᵐ ω ∂μ, X ω ∈ ({-1, 0, 1} : Set ℝ)
  /-- `χ` has mean zero. -/
  mean_zero : ∫ ω, X ω ∂μ = 0
  /-- `χ` has second moment `1/2` (so `E[χ²] = 1/2`). -/
  snd_moment : ∫ ω, (X ω) ^ 2 ∂μ = 1 / 2

/-- A random matrix `J : Ω → Matrix (Fin n) (Fin m) ℤ` is a *JL projection matrix* for the
source distribution `χ` when its entries are jointly independent and each (cast to `ℝ`) is
distributed as `χ`. This is the abstract stand-in for `J ←$ χ^{n×m}`. -/
structure IsChiMatrix {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ) (μ : Measure Ω) : Prop where
  /-- The `n·m` entries are jointly independent. -/
  indep : iIndepFun (fun p : Fin n × Fin m => fun ω => ((J ω p.1 p.2 : ℤ) : ℝ)) μ
  /-- Each entry is `χ`-distributed. -/
  entry : ∀ p : Fin n × Fin m, IsChiEntry (fun ω => ((J ω p.1 p.2 : ℤ) : ℝ)) μ

/-- Squared Euclidean norm of an integer vector, computed in `ℝ`: `‖v‖₂² = ∑ᵢ vᵢ²`.
Internal proof tool; public statements use `l2Norm` (see file header). -/
noncomputable def sqNorm {k : ℕ} (v : Fin k → ℤ) : ℝ := ∑ i, ((v i : ℝ)) ^ 2

/-- Squared Euclidean norm of a real vector: `‖v‖₂² = ∑ᵢ vᵢ²`. -/
noncomputable def sqNormR {k : ℕ} (v : Fin k → ℝ) : ℝ := ∑ i, (v i) ^ 2

/-- `sqNorm` is nonnegative (a sum of squares). -/
theorem sqNorm_nonneg {k : ℕ} (v : Fin k → ℤ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The Euclidean (ℓ₂) norm of an integer vector, in `ℝ`: `‖v‖₂ = √(∑ᵢ vᵢ²)`. This is the public
form used in the lemma statements (RoKoko Lemma 5/6 are stated on `‖·‖₂`). -/
noncomputable def l2Norm {k : ℕ} (v : Fin k → ℤ) : ℝ := Real.sqrt (sqNorm v)

/-- `l2Norm` is nonnegative. -/
theorem l2Norm_nonneg {k : ℕ} (v : Fin k → ℤ) : 0 ≤ l2Norm v := Real.sqrt_nonneg _

/-- The bridge between the public ℓ₂ norm and the internal squared norm: `‖v‖₂² = ∑ᵢ vᵢ²`. -/
theorem l2Norm_sq {k : ℕ} (v : Fin k → ℤ) : l2Norm v ^ 2 = sqNorm v :=
  Real.sq_sqrt (sqNorm_nonneg v)

/-- A nonzero integer vector has strictly positive squared norm. -/
theorem sqNorm_pos {k : ℕ} {v : Fin k → ℤ} (hv : v ≠ 0) : 0 < sqNorm v := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  refine Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ j, ?_⟩
  have : ((v j : ℝ)) ≠ 0 := by exact_mod_cast hj
  positivity

/-- The projected vector `Jw : Ω → (Fin n → ℤ)`, i.e. the random variable `ω ↦ J ω *ᵥ w`. -/
def proj {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ) (w : Fin m → ℤ) : Ω → (Fin n → ℤ) :=
  fun ω => (J ω) *ᵥ w

/-- Centered representative of `x` modulo `q` (the *balanced* residue), modelling the value the
verifier observes after the `mod q` reduction. `Int.bmod x q` lands in `[-q/2, q/2)`. -/
def centeredMod (q : ℕ) (x : ℤ) : ℤ := Int.bmod x q

/-- `‖Jw mod q‖₂`: the ℓ₂ norm of the projection after centered reduction mod `q` (the quantity the
verifier sees). -/
noncomputable def projModL2Norm {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ) (w : Fin m → ℤ)
    (q : ℕ) : Ω → ℝ :=
  fun ω => l2Norm (fun i => centeredMod q ((proj J w) ω i))

/-- The norm-distortion ratio `‖Jw‖₂ / ‖w‖₂` as a random variable (RoKoko Lemma 5 (I)). -/
noncomputable def normRatio {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ) (w : Fin m → ℤ) :
    Ω → ℝ :=
  fun ω => l2Norm ((proj J w) ω) / l2Norm w

/-- The norm ratio is the square root of the squared-norm ratio: `‖Jw‖₂/‖w‖₂ = √(‖Jw‖₂²/‖w‖₂²)`.
This is the bridge that turns the (squared) concentration of `‖Jw‖₂²` into the norm-form Lemma 5 (I). -/
theorem normRatio_eq_sqrt {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ) (w : Fin m → ℤ) (ω : Ω) :
    normRatio J w ω = Real.sqrt (sqNorm (proj J w ω) / sqNorm w) := by
  simp only [normRatio, l2Norm]
  exact (Real.sqrt_div (sqNorm_nonneg _) _).symm

/-- The `i`-th row inner product `⟨rᵢ, w⟩ = (Jw)ᵢ` as a real-valued random variable. -/
def rowInner {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ) (w : Fin m → ℤ) (i : Fin n) : Ω → ℝ :=
  fun ω => (((proj J w) ω i : ℤ) : ℝ)

/-- ℓ∞ norm of an integer vector, as a natural number: `‖v‖∞ = maxᵢ |vᵢ|`. -/
def normInf {k : ℕ} (v : Fin k → ℤ) : ℕ := Finset.univ.sup fun i => (v i).natAbs

/-- A random matrix whose entries are independent and distributed as `Bin₂` (the difference of two
independent `χ = Bin₁` variables): a.s. valued in `{-2,-1,0,1,2}`, mean `0`, second moment `1`.
This is the distribution that arises from the symmetrization `R₁ − R₂` with `R₁, R₂ ← χ` (used by
the LNP22 route, see `JL/LNP.lean`). -/
structure IsBin2Matrix {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ) (μ : Measure Ω) : Prop where
  /-- The entries are jointly independent. -/
  indep : iIndepFun (fun p : Fin n × Fin m => fun ω => ((J ω p.1 p.2 : ℤ) : ℝ)) μ
  /-- Each entry is a.s. in the `Bin₂` support `{-2,-1,0,1,2}`. -/
  mem : ∀ p : Fin n × Fin m,
    ∀ᵐ ω ∂μ, ((J ω p.1 p.2 : ℤ) : ℝ) ∈ ({-2, -1, 0, 1, 2} : Set ℝ)
  /-- `Bin₂` has mean zero. -/
  mean_zero : ∀ p : Fin n × Fin m, ∫ ω, ((J ω p.1 p.2 : ℤ) : ℝ) ∂μ = 0
  /-- `Bin₂` has second moment `1` (variance of a difference of two `χ`'s). -/
  snd_moment : ∀ p : Fin n × Fin m, ∫ ω, (((J ω p.1 p.2 : ℤ) : ℝ)) ^ 2 ∂μ = 1

/-- `‖Rw + ŷ mod q‖₂`: the ℓ₂ norm of the **masked** projection after centered reduction mod `q`.
This is the quantity the verifier sees in the LNP/LaBRADOR protocols (`z = ŷ + Rs`). -/
noncomputable def maskedProjModL2Norm {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ)
    (w : Fin m → ℤ) (yhat : Fin n → ℤ) (q : ℕ) : Ω → ℝ :=
  fun ω => l2Norm (fun i => centeredMod q ((J ω *ᵥ w) i + yhat i))

end JL
