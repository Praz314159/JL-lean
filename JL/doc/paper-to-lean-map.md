# paper-to-lean-map.md — The Johnson–Lindenstrauss lemma DAG

Living document. Exact statements, dependencies, and the paper that proves each node.
Sources are in `/papers`. Citations use the papers' own numbering.

Paper key (filenames vs. citation labels):
- `papers/rokoko.pdf` — **RoKoko** ("RoKoko: Lattice-based Succinct Arguments, a Committed
  Refinement", Klooß–Lai–Nguyen–Osadnik–Tucci). The target paper. Lemma 5, Lemma 6, Conjecture 1,
  Appendix A. (Its JL *projection results* are exactly Lemma 5/6 + Conj 1; §5.2/5.3 build the
  protocols Π_proj-c/-f on top of them, with soundness via SIS binding (Lemma 4), not new JL.)
- `papers/BS22.pdf` — **[BS23] = LaBRADOR**, Beullens & Seiler. (RoKoko cites it as [BS23]; the
  PDF is the LaBRADOR paper.) Modular JL: §4 Lemma 4.1, Lemma 4.2; full proof in its Appendix A.
- `papers/LNP22.pdf` — **[LNP22]**, Lyubashevsky–Nguyen–Plançon, "Shorter, Simpler, More General".
  JL appears as the **"approximate range proof" (ARP)**: Lemma 2.7 (ℓ∞, proven via [LNS21a]),
  Lemma 2.8 (the **χ² formulation** of the ℓ₂ bounds), Lemma 2.9/2.10 (mod-q soundness, **with a
  mask vector ŷ**). **Crucially uses a Berry–Esseen-FREE proof architecture** — see §4 below.
- `papers/GHL21.pdf` — **[GHL21/GHL22]**, Gentry–Halevi–Lyubashevsky. Origin of the modular JL
  (Corollary 3.2 ⇒ BS23 Lemma 4.1; Corollary 3.3 ⇒ BS23 Lemma 4.2). Threshold `b ≤ q/(45m)`.
- `papers/KLNO25.pdf` — downstream user / structured-projection context.

**The decisive parameter axis — the modulus threshold `b` (and what forces Berry–Esseen):**
| Source | mod-q threshold | m-dependence | needs Berry–Esseen? |
|--------|-----------------|-------------|---------------------|
| GHL21 Cor 3.3 | `b ≤ q/(45m)` | m-DEPENDENT | no (heuristic χ²) |
| LNP22 Lem 2.9 | `b ≤ q/(41m)` | m-DEPENDENT | **NO** (symmetrization + Chernoff + χ²) |
| BS23 Lem 4.2  | `b ≤ q/125`   | **m-INDEPENDENT** | **YES** (Case-3 anti-concentration) |
| RoKoko Lem 5  | `b ≤ q/b`, `b=125` | **m-INDEPENDENT** | **YES** (inherits BS23) |
The m-independence is exactly why RoKoko/BS23 pay for Berry–Esseen; LNP22 accepts an m-dependent
`b` and avoids it. **For RoKoko Conjecture 1 (which wants m-independent `b`), Berry–Esseen is the
right localization.** But LNP22's route gives a fully-rigorous, Lean-friendly *alternative* lemma
and reusable infrastructure (see N1′/N2′ below).

---

## 0. The distribution χ and the projection matrix J

χ is the distribution on {−1, 0, 1} with `Pr[χ=0] = 1/2`, `Pr[χ=1] = Pr[χ=−1] = 1/4`.
Key moments: `E[χ] = 0`, `E[χ²] = 1/2`, `E[|χ|³] = 1/2`, support bounded in `[−1,1]`.

`J ←$ χ^{n_rp × m_rp}` is a random matrix with i.i.d. χ entries. For a fixed `w ∈ ℤ^{m_rp}`,
each row `r` gives `⟨r, w⟩` with `E[⟨r,w⟩] = 0` and `E[⟨r,w⟩²] = ½‖w‖²` (cross terms vanish
since entries are independent, zero-mean). Hence `E[‖Jw‖²] = (n_rp/2)·‖w‖²`, and the typical
scale of `‖Jw‖/‖w‖` is `√(n_rp/2) = Θ(√n_rp)`.

---

## 1. The DAG

```
         GHL21 Cor 3.2/3.3 (origin, Gaussian-heuristic JL over ℤ_q)
                 │
                 ▼
   [N0] χ moments + per-row sub-Gaussianity         (leaf; Mathlib Hoeffding lemma)
                 │
        ┌────────┴─────────┐
        ▼                  ▼
   [N1] Lemma 5 (I)    [N2] Lemma 5 (II)            (BS23 Lem 4.1 / Lem 4.2)
   norm preservation   mod-q shortness soundness
   (the EASY half)     (the HARD half)
        │                  │   split into Case 1 / Case 2 / Case 3
        │                  │      Case 1  → reduces to (I)         [easy]
        │                  │      Case 2  → Chernoff on bad coords [medium]
        │                  │      Case 3  → BERRY–ESSEEN anti-conc [HARD core]
        └────────┬─────────┘
                 ▼
   [N3] Lemma 6 (I⊗J structured extension)          (RoKoko Lem 6; block-diag + union bound)
                 │
                 ▼
   [N4] Conjecture 1 (asymptotic Θ(√log 1/κ) scaling)   (RoKoko Conj 1; OPEN)
```

---

## 2. Node statements (verbatim-faithful to sources)

### [N0] χ moments and per-row sub-Gaussianity  — LEAF
For a fixed `w`, the row inner product `⟨r,w⟩ = Σᵢ rᵢ wᵢ` is a sum of independent zero-mean
variables each bounded in `[−|wᵢ|, |wᵢ|]`, hence sub-Gaussian (Hoeffding's lemma). `‖Jw‖² =
Σ_{rows} ⟨rⱼ,w⟩²` is a sum of `n_rp` i.i.d. nonneg. terms, each bounded in `[0, ‖w‖₁²]`.
- **Proven by:** elementary; Mathlib supplies `hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero`.
- **Note:** boundedness gives sub-Gaussian/sub-exponential *qualitatively*; the *tight* window
  constants need the actual second-moment/Bernstein analysis (RoKoko App A) or χ² tails (Gaussian).

### [N1] Lemma 5, inequality (I) — norm preservation  (BS23 Lemma 4.1)  — EASY HALF
For any `q ∈ ℕ`, `κ ∈ (0,1)`, there exist `n_rp, α_rp, β_rp` such that for any `m_rp` and any
nonzero `w ∈ ℤ^{m_rp}`, with `J ←$ χ^{n_rp × m_rp}`:

> `Pr[ ‖Jw‖² / ‖w‖² ∉ [α_rp, β_rp] ] ≤ κ`.

BS23 Lemma 4.1 concrete form (`κ = 2⁻¹²⁸`, `n_rp = 256`):
- `Pr[ |⟨π,w⟩| > 9.5‖w‖ ] ≲ 2⁻¹⁴¹`   (per-row, used by Case 1/3 of N2)
- `Pr[ ‖Πw‖ < √30·‖w‖ ] ≲ 2⁻¹²⁸`     (lower tail)
- `Pr[ ‖Πw‖ > √337·‖w‖ ] ≲ 2⁻¹²⁸`    (upper tail)
So `[α_rp, β_rp] = [30, 337]` for the squared ratio (`√30, √337` for the ratio of norms).
- **Proven by:** GHL21 Cor 3.2 (Gaussian heuristic) / BS23 Lem 4.1. Both tails are concentration
  of a sum of i.i.d. sub-exponential `⟨rⱼ,w⟩²`. Achlioptas [Ach01] did the ±1 analog.
- **Reachable now?** Upper tail via Mathlib Hoeffding-for-sums with LOOSE constants; tight
  `[√30,√337]` and the lower (small-ball) tail need sub-exponential Bernstein (not in Mathlib).
  See mathlib-audit.md.

### [N2] Lemma 5, inequality (II) — mod-q shortness soundness  (BS23 Lemma 4.2)  — HARD HALF
For `0 < θ ≤ q/b` and `‖w‖² ≥ θ` with `w ∈ [±q/2]^{m_rp}`:

> `Pr[ ‖Jw mod q‖² ≤ α_rp · θ ] ≤ κ`.

Concrete (BS23 Lem 4.2): for `w ∈ [±q/2]^d`, `‖w‖ ≥ b`, `b ≤ q/125`:
`Pr[ ‖Πw mod q‖ < √30·b ] ≲ 2⁻¹²⁸` (their proof gives `< 2⁻¹³⁷`). So `b = 125`.

**Proof is a case split on the geometry of `w`** (BS23 Appendix A):
- **Case 1** `‖w‖ < q/10`: no wrap-around possible (`√30·b < 0.05q`), so a small `‖Πw mod q‖`
  forces either small `‖Πw‖` (use N1 lower tail) or some row with `|⟨πᵢ,w⟩| > 0.95q` (prob
  `≤ 2⁻¹⁴¹` per row by N1), union bound over 256 rows. **Easy** — reduces to N1.
- **Case 2** `‖w‖∞ ≥ q/60`: pick coord `i` with `|wᵢ| ≥ q/60`. Conditioning on the other
  entries of a row, `|⟨π,w⟩| ≤ q/120` with prob `≤ 1/2`. Since `Σ_{i=0}^{29} C(256,i) < 2¹²⁸`,
  the prob that ≤29 rows of Πw exceed `q/120` is `< 2⁻¹²⁸`; and `√30·b < 29·q/120`. **Medium** —
  a Chernoff/binomial-tail bound on the count of "bad" coordinates.
- **Case 3** `‖w‖ ≥ q/10 ∧ ‖w‖∞ < q/60`: **THE HARD CORE.** Build `v` with `q/11 ≤ ‖v‖ < q/10`,
  `v` supported on a subset of `w`'s coords. `⟨π,v⟩` is a sum of many small independent terms
  whose distribution is close to Gaussian. Apply **Berry–Esseen** (constant 0.52 from [KS10])
  with per-summand variance `vᵢ²/2`, third moment `|vᵢ|³/2`, giving rate
  `0.52·√2·‖v‖∞/‖v‖ < 0.15`. The "bad interval" `G` has measure `2√30·b`, and the Gaussian
  width is `≥ q/11`, so `Pr[Y ∈ G] < 0.39`. Therefore per row `Pr[⟨π,v⟩ bad] ≤ 0.39 + 2·0.15 =
  0.69 < 1`, and over 256 rows `(0.69 + 2⁻¹⁴¹)²⁵⁶ < 2⁻¹³⁷`.
  - **Load-bearing constant:** `p = p(α,β) = 0.39 + 2·0.15 < 1`. The whole soundness rests on
    this per-row failure prob staying a fixed constant `< 1` (so 256 rows ⇒ `2⁻Θ(n)`).
  - **Proven by:** BS23 Lem 4.2 + Berry–Esseen (Berry 1941, Esseen 1942; constant from [KS10]).
  - **Reachable now? NO.** Berry–Esseen is absent from Mathlib (see mathlib-audit.md). This is where
    the residual `sorry` must land for both Lemma 5(II) and Conjecture 1.

### [N3] Lemma 6 — structured (I⊗J) extension  (RoKoko Lemma 6)  — CHEAP LEAF (given N1,N2)
Let `W ∈ ℤ^{m_w × r}` nonzero, `q ∈ ℕ`, `J ←$ χ^{n_rp × m_rp}`, `V := (I_{m_w/m_rp} ⊗ J)·W ∈
ℤ^{(m_w·n_rp/m_rp) × r}`. With matrix norm = max column Euclidean norm:

> `Pr[ ‖V‖²/‖W‖² ∉ [α_rp,β_rp] ] ≤ κ · r·m_w/m_rp`,
> `Pr[ ‖V mod q‖² ≤ α_rp·θ ] ≤ κ · m_w/m_rp`   (for `0<θ≤q/b`, `‖W‖²≥θ`, `W ∈ [±q/2]^{m_w×r}`).

- **Proof:** block-diagonal structure — each column `wⱼ` splits into `m_w/m_rp` chunks of height
  `m_rp`, `vⱼ,ᵢ = J·wⱼ,ᵢ`, norms add under concatenation; apply N1 per chunk + a **union bound**
  over `(i,j) ∈ [m_w/m_rp]×[r]` (first claim) and over the `≤ m_w/m_rp` nonzero chunks of the
  max-norm column (second claim). Full proof in RoKoko §A around Lemma 6.
- **Reachable now? YES, modulo N1/N2** — it is pure structural bookkeeping + `measure_union_le`.
  This is the recommended first thing to prove (it depends only on the *statements* of N1/N2).

### [N4] Conjecture 1 — asymptotic JL scaling  (RoKoko Conjecture 1)  — OPEN TARGET
There is a choice `n_rp(κ) = Θ(log(1/κ))` for which the Lemma 5 parameters scale as

> `α_rp(κ) = Θ(√log(1/κ))`,  `β_rp(κ) = Θ(√log(1/κ))`,  `b(κ) = Θ(√log(1/κ))`.

- **Status:** OPEN. RoKoko gives only a heuristic (App A): treat χ as Gaussian with matching
  mean/variance; then `‖Jw‖²` is `½‖w‖²·χ²_{n_rp}` and the scaling follows from χ² tail bounds.
  The discrete-to-Gaussian transfer for Case 3 needs Berry–Esseen with `p = p(α,β) < 1` a
  *constant* across the asymptotic regime — exactly the load-bearing analytic step.
- **Localization goal:** state N4 so the residual `sorry` is precisely "Berry–Esseen + the
  constant-`p` claim for Case 3", with explicit hypotheses. Everything else (N1 upper/lower
  tails via Bernstein, Case 1 reduction, Case 2 Chernoff) is in principle mechanical.

---

## 2b. LNP22 nodes — the Berry–Esseen-FREE route (alternative architecture)

LNP22 models JL as the **approximate range proof** with R ← Bin₁ (Bin₁ on {−1,0,1} with
`Pr[0]=1/2`, `Pr[±1]=1/4` **is exactly χ**). Its mod-q soundness uses *no* anti-concentration step.

### [L7] Lemma 2.7 — ℓ∞ approximate range proof  (from [LNS21a]) — PROVEN LEAF
For `w ∈ ℤ_q^m`, `ŷ ∈ ℤ_q^k`: `Pr_{R←Bin₁^{k×m}}[ ‖Rw + ŷ‖∞ < ½‖w‖∞ ] ≤ 2^{-k}`.
- **Proven** (not heuristic). Elementary: per row, conditioning on all but one coordinate, at most
  one of the 3 values of an entry keeps the inner product small, and `Pr` of "two of three" ≥ 1/2.
- **Reachable now**, fully rigorous — a clean independent leaf worth having in the library (goal #1).

### [L8] Lemma 2.8 — χ² formulation of the ℓ₂ norm bounds  (heuristic; GHL21 generalization)
"Under the heuristic substitution of Binκ by `N(0, κ/2)`", for `w ∈ ℤ^m`:
`Pr_{R←Binκ}[ ‖Rw‖₂ < ‖w‖₂·13·κ ] ≈ Pr_{y←χ²[256]}[y < 26] ≤ 2^{-256}` and
`Pr_{R←Binκ}[ ‖Rw‖₂ > ‖w‖₂·337·(κ/2) ] ≈ Pr_{y←χ²[256]}[y > 674] ≤ 2^{-128}`.
- This is **the same norm window as BS23** (`30`/`337`), made explicit as **χ²[256] tail bounds**.
- It is the concrete instance of RoKoko App A's "for a genuinely Gaussian J, `‖Jw‖² = ½‖w‖²·χ²_n`,
  scaling follows from χ² tails." **The heuristic gap here is the discrete→Gaussian substitution.**
- **Reachable for the GAUSSIAN model** (χ² = Gamma(n/2,2); Mathlib `Gamma` exists, tails derivable).
  The discrete Bin₁ case needs a discretization/CLT-flavored transfer (same hard nub, different form).

### [L9] Lemma 2.9 — masked mod-q soundness  (the form the protocols actually use)
Fix `m, P`, `b ≤ P/(41m)`, `w ∈ [±P/2]^m` with `‖w‖ ≥ b`, and **any** `ŷ ∈ ℤ_P^{256}`. Then
`Pr_{R←Bin₁}[ ‖Rw + ŷ mod P‖ < ½·b·√26 ] < 2^{-128}`.
- Generalizes BS23 Lemma 4.2 by the **mask vector ŷ** (lattice ZK commits `z = ŷ + Rs` w/ rejection
  sampling). RoKoko Lemma 5 has no ŷ; the ŷ lives in the protocol — but a reusable library wants it.
- **Proof = two cheap, fully-rigorous reductions (NO Berry–Esseen):**
  - **[L9a] Symmetrization (the key trick).** If the bad event has prob ≥ 2⁻¹²⁸ for one `R`, then for
    two independent `R₁,R₂←Bin₁` both bad has prob ≥ 2⁻²⁵⁶; triangle inequality (valid mod P) gives
    `‖(R₁−R₂)w mod P‖ < b√26` with prob ≥ 2⁻²⁵⁶; and `R₁−R₂ ~ Bin₂` exactly. So the masked Bin₁
    statement reduces to the **unmasked Bin₂** statement [L10]. **Elementary, Lean-friendly.**
  - **[L10] Lemma 2.10 (unmasked, Bin₂).** `Pr_{R←Bin₂}[‖Rw mod P‖ < b√26] < 2⁻²⁵⁶`, by cases:
    Case `‖w‖∞ ≥ P/4m`: Chernoff `(1/2)^256` on the rows (like BS23 Case 2). **Elementary.**
    Case `‖w‖∞ < P/4m`: no mod-reduction effect, reduces directly to **[L8]** (the χ² norm bound).
- **Reachable now EXCEPT for [L8]'s heuristic** — i.e. L9's *entire* gap collapses to the χ²/Gaussian
  norm bound, with the symmetrization + Chernoff machinery fully rigorous. This RELOCATES the
  irreducible gap from Berry–Esseen (BS23 Case 3) to the discrete→Gaussian norm transfer — but only
  at the cost of an **m-dependent** `b ≤ P/(41m)` (see the table in the header). RoKoko needs
  m-independent `b`, so it cannot take this shortcut for Conjecture 1.

---

## 3. Where the `sorry`s should land (localization map)
| Node | Residual gap | Honest path |
|------|--------------|-------------|
| N0   | none (tight constants only) | Mathlib Hoeffding lemma |
| N1   | tight `[√30,√337]` + lower tail | sub-exponential Bernstein (build) OR χ² tails (Gaussian model) |
| N2 Case 1 | none | reduce to N1 |
| N2 Case 2 | none | binomial/Chernoff tail (Mathlib) |
| N2 Case 3 | **Berry–Esseen + `p<1` constant** | ← THE irreducible `sorry` (for m-INDEPENDENT `b`) |
| N3   | none | union bound (Mathlib) |
| N4   | **same Berry–Esseen + constant-`p` across κ** | ← THE irreducible `sorry` |
| L7   | none | elementary per-row argument (fully rigorous) |
| L8   | discrete→Gaussian χ² substitution | χ² tails for Gaussian model (Gamma, Mathlib) + discretization |
| L9a  | none | symmetrization: Bin₁−Bin₁=Bin₂ + triangle ineq (fully rigorous) |
| L10  | only via L8 | Chernoff case + reduce to L8 |
| L9   | only via L8 (NO Berry–Esseen) | L9a + L10; m-DEPENDENT `b ≤ P/41m` |

**Two architectures, two distinct irreducible gaps:**
1. **RoKoko/BS23 (m-independent `b`):** gap = **Berry–Esseen** anti-concentration (N2 Case 3, N4).
2. **LNP22 (m-dependent `b`):** gap = **discrete→Gaussian χ² substitution** (L8); the mask handling
   (L9a) and the case split (L10) are fully rigorous and Lean-friendly.

The project succeeds if every node except its architecture's single gap is proven (or cleanly
reduced to Mathlib), and that gap is one sharply-stated, annotated `sorry`. RoKoko Conjecture 1
specifically needs route 1 (its `b` is m-independent), so **Berry–Esseen remains the target gap for
the headline result** — but the LNP22 route (L7, L9a, L10) is the recommended source of cheap,
fully-rigorous wins and reusable infrastructure, and L8 (χ² tails, Gaussian model) is the more
Lean-tractable of the two gaps if we want a rigorously-closed *variant* of the lemma.
