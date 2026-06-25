# Changelog

All notable changes to `JL-lean`. Format loosely follows Keep a Changelog.

## [Unreleased]

### Added
- **Project foundation** aligned with the sibling `z-lean` conventions, designed standalone but
  monorepo-ready for a future lattice-crypto formalization effort.
  - Lean 4 + Mathlib `v4.31.0` project; `lake build` green.
  - **0 `sorry`, 0 `axiom`**, CI-enforced over `JL/` (`.github/workflows/ci.yml`).
  - Probability model (measure-theoretic): `IsChiEntry`, `IsChiMatrix`, `IsBin2Matrix`, plus
    geometry (`sqNorm`, `proj`, `ratio`, `centeredMod`, `normInf`, masked projection).
  - The lemma DAG encoded in the no-`sorry` idiom: the irreducible analytic gap as
    `BerryEsseenHyp : Prop` (+ `ChiSquaredTailHyp`); headline nodes as `…_Statement : Prop` targets;
    the open conjecture behind a `JLRegime` tag.
  - Two literature routes stated: RoKoko/BS23 (`JL/RoKoko.lean`) and the Berry–Esseen-free LNP22
    route (`JL/LNP.lean`).
  - Docs: `JL/doc/paper-to-lean-map.md` (DAG + paper→Lean), `JL/doc/mathlib-audit.md` (Mathlib
    coverage + go/no-go), `JL/doc/stability.md` (tiers); `AGENTS.md` (⇄ `CLAUDE.md`); Apache `LICENSE`.

### Notes
- Toolchain pinned at `v4.31.0` (newer than z-lean's `v4.30.0-rc2`); reconciled upward at monorepo
  time.
- Nothing is proved yet by design — this release is the audited *foundation*. See `doc/stability.md`
  for what is a target vs. an assumed analytic input.
