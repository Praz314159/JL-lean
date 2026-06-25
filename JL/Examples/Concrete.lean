/-
Copyright (c) 2026. Released under Apache 2.0 license.
JL-lean: formal verification of the lattice Johnson–Lindenstrauss projection lemmas.
-/
import JL.RoKoko
import JL.Regime

/-!
# Concrete BS23 parameter instance

The fully-specified parameter set proven in BS23 Lemmas 4.1/4.2 and adopted by RoKoko Lemma 5 at
`κ = 2⁻¹²⁸`: `n_rp = 256`, `[α_rp, β_rp] = [30, 337]` (squared ratio), `b = 125`. Exposed as a
`Params` value plus the concrete `Lemma5_*` claims it instantiates. In the `JL.Examples` library
(built in CI, not in `import JL`).

**Stability: concrete parameters; the discharging Lean proof still depends on the assumed analytic
inputs** (`JL.Analytic.BerryEsseenHyp`). Tagged `JL.JLRegime.concrete`.
-/

namespace JL.Examples

/-- The BS23 / RoKoko concrete parameters at `κ = 2⁻¹²⁸`. -/
def bs23Params : JL.Params := { n := 256, α := 30, β := 337, b := 125 }

/-- Target failure probability for the concrete instance, `κ = 2⁻¹²⁸`. -/
noncomputable def kappa128 : ℝ := (2 : ℝ) ^ (-(128 : ℤ))

/-- The concrete norm-preservation claim (BS23 Lemma 4.1) is an instance of the N1 target. -/
def concreteNormPreservation : Prop := JL.Lemma5_NormPreservation kappa128 (q := 2 ^ 32)

/-- The concrete mod-q soundness claim (BS23 Lemma 4.2) is an instance of the N2 target. -/
def concreteModqSoundness : Prop := JL.Lemma5_ModqSoundness kappa128 (q := 2 ^ 32)

/-- The regime tag for the concrete instance: `concrete`. -/
def concreteRegime : JL.JLRegime := JL.JLRegime.concrete

end JL.Examples
