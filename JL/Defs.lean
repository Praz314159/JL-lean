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
JL development (see `LEMMAS.md` for the lemma DAG and `AUDIT.md` for the Mathlib coverage).

Design choices (per project kickoff):
* **Abstract probability model.** The projection matrix `J` is an arbitrary measurable map
  `Ω → Matrix (Fin n) (Fin m) ℤ` on a generic probability space, whose entries are required to be
  independent (`iIndepFun`) and each distributed as the JL source distribution `χ`
  (`IsChiEntry`). This matches Mathlib's `ProbabilityTheory.HasSubgaussianMGF` API for maximal
  reuse, while a concrete `χ` can be supplied later as one instance of `IsChiEntry`.
* **Integer entries, real norms.** `J` and the witness `w` are integer-valued (χ is supported on
  `{-1,0,1}` and `w ∈ ℤ^m`); squared norms are computed in `ℝ` via casts. This keeps the
  `mod q` reduction (`Int.emod`/centered representative) and the sub-Gaussian analysis on the
  same objects.
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

/-- Squared Euclidean norm of an integer vector, computed in `ℝ`: `‖v‖² = ∑ᵢ vᵢ²`. -/
noncomputable def sqNorm {k : ℕ} (v : Fin k → ℤ) : ℝ := ∑ i, ((v i : ℝ)) ^ 2

/-- Squared Euclidean norm of a real vector: `‖v‖² = ∑ᵢ vᵢ²`. -/
noncomputable def sqNormR {k : ℕ} (v : Fin k → ℝ) : ℝ := ∑ i, (v i) ^ 2

/-- The projected vector `Jw : Ω → (Fin n → ℤ)`, i.e. the random variable `ω ↦ J ω *ᵥ w`. -/
def proj {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ) (w : Fin m → ℤ) : Ω → (Fin n → ℤ) :=
  fun ω => (J ω) *ᵥ w

/-- Centered representative of `x` modulo `q` (the *balanced* residue), modelling the value the
verifier observes after the `mod q` reduction. `Int.bmod x q` lands in `[-q/2, q/2)`. -/
def centeredMod (q : ℕ) (x : ℤ) : ℤ := Int.bmod x q

/-- `‖Jw mod q‖²`: squared norm of the projection after centered reduction mod `q`. -/
noncomputable def projModSqNorm {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ) (w : Fin m → ℤ)
    (q : ℕ) : Ω → ℝ :=
  fun ω => sqNorm (fun i => centeredMod q ((proj J w) ω i))

/-- The norm-distortion ratio `‖Jw‖² / ‖w‖²` as a random variable. -/
noncomputable def ratio {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ) (w : Fin m → ℤ) : Ω → ℝ :=
  fun ω => sqNorm ((proj J w) ω) / sqNorm w

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

/-- `‖Rw + ŷ mod q‖²`: squared norm of the **masked** projection after centered reduction mod `q`.
This is the quantity the verifier sees in the LNP/LaBRADOR protocols (`z = ŷ + Rs`). -/
noncomputable def maskedProjModSqNorm {n m : ℕ} (J : Ω → Matrix (Fin n) (Fin m) ℤ)
    (w : Fin m → ℤ) (yhat : Fin n → ℤ) (q : ℕ) : Ω → ℝ :=
  fun ω => sqNorm (fun i => centeredMod q ((J ω *ᵥ w) i + yhat i))

end JL
