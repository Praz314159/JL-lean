# `References/` — reserved

Root-level home for **Lean specs / pinned reference statements of external results** that JL-lean
depends on but does not prove in-tree — e.g. the precise form of the Berry–Esseen inequality, χ²
tail bounds, or any primitive a future monorepo sibling would discharge.

Currently empty by design. The assumed analytic inputs presently live as `…Hyp : Prop` definitions
in [`../JL/Analytic/`](../JL/Analytic/); when one is either (a) proved in Mathlib upstream or (b)
given a self-contained Lean spec here, its `Hyp` should be re-expressed against that reference and
this directory should gain the corresponding `*/Spec.lean`.

## Planned

```
References/
├── BerryEsseen/Spec.lean   -- the Lyapunov-form quantitative CLT, pinned to a literature constant
│                              (Korolev–Shevtsova ≤ 0.5600). Discharges JL.Analytic.BerryEsseenHyp.
└── ChiSquared/Spec.lean    -- χ²_n = Gamma(n/2, 2) tail bounds. Discharges JL.Analytic.ChiSquaredTailHyp.
```
