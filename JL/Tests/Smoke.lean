/-
Copyright (c) 2026. Released under Apache 2.0 license.
JL-lean: formal verification of the lattice Johnson–Lindenstrauss projection lemmas.
-/
import JL.Defs

/-!
# Smoke tests for the computable model primitives

`#eval` / `native_decide` oracle checks pinning the behaviour of the computable definitions
(`normInf`, `centeredMod`). In the `JL.Tests` library — the only place `native_decide` is allowed
(`AGENTS.md`). These backstop refactors of the model defs.
-/

namespace JL.Tests

/-- `‖(3, -5, 2)‖∞ = 5`. -/
example : JL.normInf ![(3 : ℤ), -5, 2] = 5 := by native_decide

/-- `‖0‖∞ = 0` (empty/zero vector edge case). -/
example : JL.normInf ![(0 : ℤ), 0, 0] = 0 := by native_decide

/-- Balanced residue: `10 ≡ 3 (mod 7)`, and `3 ∈ [-3, 3)`. -/
example : JL.centeredMod 7 10 = 3 := by native_decide

/-- Balanced residue wraps to negative: `5 ≡ -2 (mod 7)`. -/
example : JL.centeredMod 7 5 = -2 := by native_decide

/-- Balanced residue is `0` on multiples of the modulus. -/
example : JL.centeredMod 7 14 = 0 := by native_decide

end JL.Tests
