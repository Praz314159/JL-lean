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

## Note on the two analytic halves (Ach01 vs Berry–Esseen)

RoKoko Appendix A's asymptotic argument is a *heuristic* that "treats the discrete χ over `{-1,0,1}`
as if it were a Gaussian." That heuristic decomposes into two halves with **different** rigorous
status, and our `…Hyp` localization reflects this:

- **Concentration (norm preservation, Pillar 1).** Rigorous for discrete χ via **Achlioptas
  [Ach01, *Database-friendly random projections*, JCSS 2003, Lemma 5.1/5.2]**: the moments of
  `⟨r,a⟩` are dominated by the Gaussian's, yielding the same Bernstein/χ² two-sided tail. Underwrites
  `SqNormConcentrationHyp` / `ChiSquaredTailHyp`; the `Θ(√log)` window scaling is *not* conjectural.
- **Anti-concentration (mod-`q` small-ball, Pillar 2 / Case 3).** Ach01 gives nothing here. This is
  the genuine heuristic leap; we make it rigorous-modulo-two-standard-facts by carrying
  `BerryEsseenHyp` (quantitative χ→Gaussian CDF transfer, error `esseenConst·L/√v`) and
  `GaussianSmallBallHyp` (the Gaussian small-ball, RoKoko's `0.39`). The conjecture reduces to the
  single constant inequality `0.39 + 2·0.15 < 1` holding uniformly across the regime.
