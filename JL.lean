/-
Copyright (c) 2026. Released under Apache 2.0 license.
JL-lean: formal verification of the lattice Johnson–Lindenstrauss projection lemmas.

Public umbrella. Imports the stable model + the two route statements + the analytic hypotheses and
the regime tag. Does NOT import `JL.Research`, `JL.Examples`, or `JL.Tests` (separate libraries,
built in CI but excluded here so downstream `import JL` stays lean).
-/
import JL.Defs
import JL.Regime
import JL.Analytic.BerryEsseen
import JL.Analytic.ChiSquared
import JL.RoKoko
import JL.LNP
