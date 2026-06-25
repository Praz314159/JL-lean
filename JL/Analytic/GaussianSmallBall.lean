/-
Copyright (c) 2026. Released under Apache 2.0 license.
JL-lean: formal verification of the lattice Johnson–Lindenstrauss projection lemmas.
-/
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Gaussian central small-ball — the second irreducible analytic input of Case 3

`GaussianSmallBallHyp` is the Gaussian *anti-concentration* fact underlying BS23 Lemma 4.2 Case 3,
stated as a `Prop`-valued abbreviation (the `…Hyp` idiom of `AGENTS.md`). Mathlib has no bound on the
mass a Gaussian places on an interval (no density-peak / interval-mass lemma — see
`JL/doc/mathlib-audit.md`), and this is **not** derivable from Berry–Esseen, which only compares
CDFs. It is the second load-bearing analytic input of Case 3, alongside `JL.Analytic.BerryEsseenHyp`.

**Why a single interval, not the periodic mod-`q` union.** The per-row bad event is
`⟨rᵢ,w⟩ mod q ∈ [-c, c]`, i.e. `⟨rᵢ,w⟩` lands in the `q`-periodic union `⋃ₖ [kq+t-c, kq+t+c]`. In the
Case-3 proof this union is split: the **single interval nearest the Gaussian mean** is controlled by
this small-ball bound, while the **wrap-around** (all other, far-tail intervals) is controlled by the
sub-Gaussian tail of `⟨rᵢ,w⟩` — which is `JL.N0` (`n0_rowSubgaussian`), already proved. So the
Gaussian-specific irreducible content is exactly the *central* small-ball; the periodicity is handled
by concentration we already have. This is what keeps RoKoko's per-row bound at `0.39 + 2·0.15 < 1`
(one Berry–Esseen application, not one per interval).

`p₀ < 1` (held uniform across the regime) is the constant the bound must deliver; it is kept an
abstract parameter so the constant chase (`p₀ + 2·esseenConst·L/√v + sub-Gaussian tail < 1`) lives in
*instantiating* the hypothesis, not in its statement.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace JL.Analytic

/-- The shortness threshold `c = α·θ` must be a small fraction of the modulus for the central
small-ball constant to stay below `1`. Via the anti-concentration regime `α ≤ c₀·b` and `θ ≤ q/b`
this is `c ≤ c₀·q`; `smallBallSlack` is that `c₀`. -/
noncomputable def smallBallSlack : ℝ := 1 / 30

/-- **Gaussian central small-ball, as a named hypothesis.** For a centered real Gaussian `N(0,v)`
whose standard deviation lies in the Case-3 variance window `√v ∈ [q/(11√2), q/(10√2)]` (produced by
the sub-vector construction, `v = ½‖w_T‖₂²` with `‖w_T‖₂ ∈ [q/11, q/10)`), the mass it puts on ANY
single interval of half-width `c` — uniformly over the centre `t` — is `≤ p₀`, provided `c` is a small
fraction of the modulus (`c ≤ smallBallSlack · q`).

This is RoKoko's `0.39`. See the module docstring for why the periodic wrap-around is *not* part of
this statement (it is handled by the sub-Gaussian tail of the row inner product, `JL.N0`). -/
def GaussianSmallBallHyp (q : ℕ) (p₀ : ℝ) : Prop :=
  ∀ v : NNReal,
    ((q : ℝ) / (11 * Real.sqrt 2)) ^ 2 ≤ (v : ℝ) →
    (v : ℝ) ≤ ((q : ℝ) / (10 * Real.sqrt 2)) ^ 2 →
    ∀ c t : ℝ, 0 ≤ c → c ≤ smallBallSlack * q →
      (gaussianReal 0 v).real (Set.Icc (t - c) (t + c)) ≤ p₀

end JL.Analytic
