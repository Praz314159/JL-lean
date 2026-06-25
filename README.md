# JL-lean — formal verification of the lattice Johnson–Lindenstrauss projection lemmas

A Lean 4 + Mathlib library of the ring Johnson–Lindenstrauss (JL) projection lemmas (the lattice
"approximate range proof") underpinning LaBRADOR, LNP22, KLNO25, SALSAA, and RoKoko, culminating in
**RoKoko Conjecture 1** (asymptotic JL scaling).

Built standalone but **monorepo-ready**, mirroring the conventions of the sibling `z-lean`
(sumcheck / linear-codes) repo, so the two can later merge into one lattice-crypto formalization
effort. Contributor & AI policy: [`AGENTS.md`](AGENTS.md) (⇄ `CLAUDE.md`).

## Status
- **Builds green** on Lean `v4.31.0` + Mathlib `v4.31.0` (`lake build`).
- **0 `sorry`, 0 `axiom`**, CI-enforced over all of `JL/` ([`.github/workflows/ci.yml`](.github/workflows/ci.yml)).
- The full JL lemma DAG is stated; nothing is proved yet by design — this is the audited
  *foundation*. Unproven things are explicit: analytic gaps are `…Hyp : Prop`, headline targets are
  `…_Statement : Prop`, the open conjecture is a `JLRegime` tag. See
  [`JL/doc/stability.md`](JL/doc/stability.md).
- The whole development localizes to **one irreducible analytic gap, Berry–Esseen**
  (`JL.Analytic.BerryEsseenHyp`); the second route (LNP22) relocates its only gap onto the
  *derivable* χ² tail (`JL.Analytic.ChiSquaredTailHyp`).

## What you import
```lean
import JL   -- model + analytic hypotheses + regime tag + RoKoko/LNP route statements
```
`JL.Research`, `JL.Examples`, `JL.Tests` are separate libraries (built in CI, not pulled in by `import JL`).

## Layout
| Path | Contents |
|------|----------|
| `JL/Defs.lean` | Probability model (`IsChiEntry`, `IsChiMatrix`, `IsBin2Matrix`) + geometry (`sqNorm`, `proj`, `ratio`, `centeredMod`, `normInf`, `maskedProjModSqNorm`) |
| `JL/Analytic/BerryEsseen.lean` | `BerryEsseenHyp` — the irreducible gap (quantitative CLT) |
| `JL/Analytic/ChiSquared.lean` | `ChiSquaredTailHyp` — the derivable gap (χ² = Gamma(n/2,1/2) tails) |
| `JL/RoKoko.lean` | RoKoko/BS23 route targets: `N0_RowSubgaussian`, `Lemma5_NormPreservation`, `Lemma5_ModqSoundness`, `Lemma6_Structured` |
| `JL/LNP.lean` | LNP22 Berry–Esseen-free route: `Arp_Linf` (L7), `Lnp_ModqUnmasked` (L10), `Lnp_ModqMasked` (L9), `Symmetrization` (L9a) |
| `JL/Regime.lean` | `JLRegime` (`concrete \| conjectured`) tag |
| `JL/Research/Conjecture.lean` | `Conjecture1_Statement` (asymptotic scaling, conjectured) |
| `JL/Examples/Concrete.lean` | BS23 concrete instance (`κ=2⁻¹²⁸`, `n=256`, `[30,337]`, `b=125`) |
| `JL/Tests/Smoke.lean` | `#eval`/`native_decide` checks of the computable primitives |
| `JL/doc/` | `paper-to-lean-map.md` (the DAG), `mathlib-audit.md` (coverage), `stability.md` (tiers) |
| `papers/` | Source PDFs (RoKoko, BS22=LaBRADOR, GHL21, KLNO25, LNP22) |

## Build
```
lake exe cache get   # fetch prebuilt Mathlib (first time only)
lake build
```

## License
Apache License 2.0. See [`LICENSE`](LICENSE).
