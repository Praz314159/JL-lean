/-
Copyright (c) 2026. Released under Apache 2.0 license.
JL-lean: formal verification of the lattice Johnson–Lindenstrauss projection lemmas.
-/

/-!
# Parameter-scaling regime tag

`JLRegime` records, for a JL parameter claim, whether the scaling is machine-checked or only
conjectured — mirroring z-lean's `ProximityRegime` (`proven | conjectured`). Downstream parameter
selectors pattern-match on it; the `conjectured` branch flags reliance on RoKoko Conjecture 1
(asymptotic `Θ(√log(1/κ))` scaling), which reduces to `JL.Analytic.BerryEsseenHyp`.
-/

namespace JL

/-- Which tier a JL parameter-scaling claim sits in.

* `concrete` — a fixed, fully-specified instance (e.g. `κ = 2⁻¹²⁸`, `n = 256`, `[α,β] = [30,337]`,
  `b = 125`), as proven in BS23 Lemmas 4.1/4.2. **Stability: the parameters are concrete; their
  Lean proof still depends on the assumed analytic inputs (`BerryEsseenHyp`).**
* `conjectured` — the asymptotic `Θ(√log(1/κ))` scaling of RoKoko Conjecture 1. **Stability:
  research / conjectured** — not backed by a Lean theorem; reduces to `BerryEsseenHyp` plus
  mechanical scaling. See `JL/Research/Conjecture.lean`.

Pattern matches should treat this as open and include a `_` default; a third (e.g.
Gaussian-model-rigorous) tier may be added. -/
inductive JLRegime where
  | concrete
  | conjectured
  deriving DecidableEq, Repr

end JL
