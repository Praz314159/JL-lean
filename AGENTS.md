# AGENTS.md — Contributor & AI-Assistant Policy

Guidance for both human contributors and AI assistants (Claude Code, Cursor, Copilot, …) working on
this repo. Symlinked to `CLAUDE.md` for Claude-specific tooling. Conventions deliberately track the
sibling `z-lean` (sumcheck/linear-codes) repo so the two can later merge into one lattice-crypto
monorepo with zero friction.

## What this is

`JL-lean` is a Lean 4 + Mathlib library of the lattice **Johnson–Lindenstrauss (JL) projection
lemmas** (the "approximate range proof") underpinning LaBRADOR, LNP22, KLNO25, SALSAA, and RoKoko,
culminating in **RoKoko Conjecture 1** (asymptotic JL scaling). Goals, in priority order:
1. a reusable, kernel-checked JL-projection library; 2. precise *localization* of Conjecture 1 onto
its single load-bearing analytic gap (Berry–Esseen).

## Repo layout (at-a-glance)

- [`JL/Defs.lean`](JL/Defs.lean) — the probability model (`IsChiEntry`, `IsChiMatrix`,
  `IsBin2Matrix`) and geometry (`l2Norm`, `sqNorm`, `proj`, `normRatio`, `projModL2Norm`,
  `centeredMod`, `normInf`, masked proj). Bounds are stated on the ℓ₂ norm (`l2Norm`), squared
  internally via `l2Norm_sq`.
- [`JL/Analytic/`](JL/Analytic/) — the analytic inputs that are *assumed*, not proved here:
  `BerryEsseen.lean` (`BerryEsseenHyp`), `ChiSquared.lean` (`ChiSquaredTailHyp`). These are the
  localized gaps; everything downstream consumes them as explicit hypotheses.
- [`JL/RoKoko.lean`](JL/RoKoko.lean) — the RoKoko/BS23 route: nodes N0–N3 (Lemma 5 (I)/(II), Lemma 6).
- [`JL/LNP.lean`](JL/LNP.lean) — the LNP22 (Berry–Esseen-free) route: L7, L9/L9a/L10.
- [`JL/Regime.lean`](JL/Regime.lean) — `JLRegime` (`proven | conjectured`) à la z-lean's
  `ProximityRegime`; tags which parameter scaling is machine-checked vs. conjectural.
- [`JL/Research/`](JL/Research/) — exploratory / target statements (Conjecture 1). Built in CI, **not**
  pulled into `import JL`.
- [`JL/Examples/`](JL/Examples/) — concrete instantiations (the `κ=2⁻¹²⁸`, `n=256` instance).
- [`JL/Tests/`](JL/Tests/) — `#eval` / `native_decide` smoke checks.
- [`JL/doc/`](JL/doc/) — `paper-to-lean-map.md` (the lemma DAG), `mathlib-audit.md` (coverage),
  `stability.md` (tiers).

## Build & validation

- Lean toolchain pinned at [`lean-toolchain`](lean-toolchain) (`v4.31.0`); Mathlib pinned to the
  matching `v4.31.0` in [`lakefile.toml`](lakefile.toml). Bump deliberately. (z-lean is currently on
  `v4.30.0-rc2`; at monorepo time we reconcile **upward** to the newer stable pin.)
- `lake exe cache get` then `lake build` must be green.
- **CI rejects proof-term `sorry` and user-declared `axiom`** across all of `JL/`. See
  [`.github/workflows/ci.yml`](.github/workflows/ci.yml).
- `native_decide` is allowed **only in `JL/Tests/`**, where it backstops `#eval` oracle vectors.

## The no-`sorry` discipline (read this before adding a statement)

We never commit a `sorry`, not even on a work-in-progress branch. Encode unproven things explicitly:

- **An analytic input we will not prove here** (e.g. Berry–Esseen, a χ² tail): a `Prop`-valued
  abbreviation named `…Hyp`, e.g. `def BerryEsseenHyp : Prop := ∀ …`. Downstream theorems take it as
  a named hypothesis `(hBE : BerryEsseenHyp)`. The dependency is then type-enforced and visible.
- **A headline result we intend to prove but haven't yet**: a `Prop`-valued *target* named
  `…_Statement`, e.g. `def Lemma5_NormPreservation (…) : Prop := …`. When proved, add a `theorem`
  (lowerCamel) discharging it: `theorem lemma5_norm_preservation … : Lemma5_NormPreservation … := …`,
  and update `doc/stability.md`.
- **An open conjecture**: a `JLRegime` variant + a `…_Statement` in `JL/Research/`, with
  **`Stability: research / conjectured`** in the first docstring line.

## Coding conventions

- `Type*` for universe binders unless a definition genuinely needs `Type 0`.
- **Narrowed theorems:** if a result is weaker than its name suggests (round-0 only, loose constants,
  conditional on a `…Hyp`), put the qualifier in the **first line** of the docstring.
- Prefer `simp only [...]` over bare `simp` in proof-critical paths (calc steps, rewrites under
  binders). Bare `simp` is fine in `decide`-style closers.
- No `@[simp]` on `instance` or `def` declarations — put it on lemmas (use a companion unfold lemma).
- A bare `set_option maxHeartbeats <N>` above the default (200000) outside `Tests/` needs a comment
  with the root cause.
- Probability is **measure-theoretic** (Mathlib `MeasureTheory.Measure` / `ProbabilityTheory`); the
  source distribution χ is a finite `PMF` exposed via `PMF.toMeasure`. (This differs from z-lean's
  finite-counting `ℚ` style for sumcheck — JL's bounds are analytic and require the measure stack.)

## Branch & PR hygiene

- `main` is the publishable line; feature work on `topic/<name>` branches; AI proof exploration on
  `ai-prover-<timestamp>` branches. One concern per PR (refactors separate from proof additions).
