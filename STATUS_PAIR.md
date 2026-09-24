# Status: at least one of ζ₂(7), ζ₂(9) is irrational (the pair programme)

Updated 2026-09-24 by the integrator after prove round 1. The previous state is commit `3ba9c24`
(blueprint and audit; every routine proof file except `NonvanishingLS` was a `sorry` stub).
Plan and statement map: `BLUEPRINT_PAIR.md`.

## Headline

* `bash scripts/build.sh Zeta2Lean.Pair.Main` is **green** (8952 jobs, exit 0).
  `bash scripts/build.sh Zeta2Lean` (both theorems) is also green (8975 jobs, exit 0).
* All routine lemmas of the pair are now proved except one, GAP 4 (`Valuation_proof`). The five
  reused sibling files are proved too.
* **4 `sorry` are left in the pair**, one per file:
  * `Valuation` (GAP 4): a proof obligation of the main theorem, expected to be routine.
  * `Growth` (GAP 1), `Denominators` (GAP 2) and `Nonvanishing` (GAP 3): open research gaps. They
    are **hypotheses** of the main theorem, so their stubs enter only the `_uncond` variant.
* `scripts/audit.sh` finds **no forbidden construct**.
* `#print axioms` (end of `Zeta2Lean/Pair/Main.lean`):

```
'Zeta2.Pair.zeta2_7_9_not_both_rational' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
'Zeta2.Pair.zeta2_7_9_not_both_rational_uncond' depends on axioms: [propext, sorryAx, Classical.choice, Quot.sound]
```

  In the main theorem, `sorryAx` comes **only from the `Valuation_proof` stub**. With
  `Stmt_Valuation` as an extra hypothesis, the same assembly has only the standard axioms:

```lean
theorem integrator1_main_mod_valuation (hPNT : PNT_Stmt) (hVal : Stmt_Valuation)
    (hGrowth : Stmt_Growth configE gE) (hDen : Stmt_Denominators configE deltaE)
    (hNV : Stmt_Nonvanishing configE) : PairStatement :=
  main_of_stmts configE gE deltaE marginE JConv_proof L1_full hVal Criterion_proof hGrowth hDen
    hNV hPNT
-- 'Zeta2.Pair.integrator1_main_mod_valuation' depends on axioms: [propext, Classical.choice, Quot.sound]
```

  This theorem was checked in a scratch file and is not part of the library. The scratch file was
  deleted; a copy is in the integrator's scratchpad track `pair79/integrator1/`.

**The theorem is not proved.** Even once GAP 4 is done, it remains conditional on the three open
gaps, and on PNT, which is cited.

## What the main theorem depends on now

```lean
theorem Zeta2.Pair.zeta2_7_9_not_both_rational (hPNT : PNT_Stmt) (hGrowth : Stmt_Growth configE gE)
    (hDen : Stmt_Denominators configE deltaE) (hNV : Stmt_Nonvanishing configE) :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧
      ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q))
```

1. **Lean kernel + Mathlib** (`v4.35.0-rc2`). Axioms: `propext`, `Classical.choice`, `Quot.sound`.
2. **One proof stub:** `Valuation_proof : Stmt_IntegrandTaylor → Stmt_Delta → Stmt_DeltaFun →
   Stmt_Valuation` (GAP 4). Its three hypotheses are all proved.
3. **Cited hypothesis:** `PNT_Stmt` (`ψ(x)/x → 1`). Only `Stmt_Denominators` consumes it.
4. **Three open gap hypotheses:** `Stmt_Growth configE gE`, `Stmt_Denominators configE deltaE`
   and `Stmt_Nonvanishing configE`. In the `_LS` variant the last is replaced by the arithmetic
   `Stmt_LaiSprangCond configE`.
5. **Trusted definitions in the conclusion** (sibling `Defs.lean`): `volkenbornSum`,
   `HasVolkenborn`, `halfPow`, `J`, `zeta2`.
   * The gap hypotheses are stated with the pair objects `rho0`, `Z7`, `Z9`, `integrand`,
     `ClearsDen` and `configE`.
   * These objects do not affect the validity of the implication. They do decide whether the gap
     hypotheses are true, and hence provable. They were audited against the mathematics
     (`BLUEPRINT_PAIR.md`, "Audit").
6. **One cited identification, not formalised:** `zeta2 s = J(s-1)/((s-1)2^s)` (LSZ Lemma 2.8).
   This is the same as in the sibling; see its `STATUS.md`.

## Per-file census

| file | theorem : Stmt | deps (hypotheses) | sorry | lines | status |
|---|---|---|---|---|---|
| `Pair/Proofs/GenLinearForm` | `GenLinearForm_proof : Stmt_GenLinearForm` | JConv, Translation | 0 | 109 | done (round 1) |
| `Pair/Proofs/PartialFractions` | `PF_proof : Stmt_PF` | – | 0 | 353 | done (round 1) |
| `Pair/Proofs/CoeffVanish` | `CoeffVanish_proof : Stmt_CoeffVanish` | PF | 0 | 279 | done (round 1) |
| `Pair/Proofs/LinearForm` | `L1_proof : Stmt_L1` | GenLinearForm, CoeffVanish | 0 | 63 | done (round 1) |
| `Pair/Proofs/IntegrandTaylor` | `IntegrandTaylor_proof : Stmt_IntegrandTaylor` | PF | 0 | 91 | done (round 1) |
| `Pair/Proofs/CrudeIntegrality` | `CrudeInt_proof : Stmt_CrudeInt` | – | 0 | 407 | done (round 1) |
| `Pair/Proofs/NonvanishingLS` | `Nonvanishing_of_LaiSprang : Stmt_LaiSprangCond cfg → Stmt_Nonvanishing cfg`; `frequently_prime_forty_mul_sub_one(_gt)` | L1 | 0 | 171 | done (before round 1) |
| `Pair/Proofs/Valuation` | `Valuation_proof : Stmt_Valuation` (**GAP 4**) | IntegrandTaylor, Delta, DeltaFun | 1 | 79 | **stub**: routine, next round |
| `Pair/Proofs/Growth` | `Growth_proof : Stmt_Growth configE gE` (**GAP 1**) | PF, CoeffVanish | 1 | 91 | open gap (hypothesis) |
| `Pair/Proofs/Denominators` | `Denominators_proof : Stmt_Denominators configE deltaE` (**GAP 2**) | PF, CoeffVanish, CrudeInt | 1 | 86 | open gap (hypothesis) |
| `Pair/Proofs/Nonvanishing` | `Nonvanishing_proof : Stmt_Nonvanishing configE` (**GAP 3**) | L1, IntegrandTaylor, Delta, DeltaFun, PF, CoeffVanish, CrudeInt | 1 | 83 | open gap (hypothesis) |
| `Proofs/JConvergence` (reused) | `JConv_proof : Stmt_JConv` | – | 0 | 217 | done (synced from sibling) |
| `Proofs/Translation` (reused) | `Translation_proof : Stmt_Translation` | – | 0 | 148 | done (synced from sibling) |
| `Proofs/Criterion` (reused) | `Criterion_proof : Stmt_Criterion` | – | 0 | 148 | done (synced from sibling) |
| `Proofs/DeltaCalculus` (reused) | `Delta_proof : Stmt_Delta` | – | 0 | 220 | done (synced from sibling) |
| `Proofs/DeltaFunctions` (reused) | `DeltaFun_proof : Stmt_DeltaFun` | Delta | 0 | 327 | done (synced from sibling) |
| `Pair/Assembly.lean` | `main_of_stmts`, `marginE`, `Sn_eq_Lform`, … | JConv, L1, Valuation, Criterion, 3 gaps, PNT | 0 | 215 | done (blueprint) |
| `Pair/Main.lean` | `zeta2_7_9_not_both_rational` (+ 3 variants) | PNT, 3 gaps | 0 | 92 | done, modulo the `Valuation` stub |

* **Axioms of the proved theorems.** `#print axioms` gives `[propext, Classical.choice, Quot.sound]`
  for each of the following:
  * pair: `GenLinearForm_proof`, `PF_proof`, `CoeffVanish_proof`, `L1_proof`, `L1_full`,
    `IntegrandTaylor_proof`, `CrudeInt_proof`, `Nonvanishing_of_LaiSprang`,
    `frequently_prime_forty_mul_sub_one_gt`, `main_of_stmts`, `marginE`;
  * reused: `JConv_proof`, `Translation_proof`, `Criterion_proof`, `Delta_proof`,
    `DeltaFun_proof`.
* **Exact types.** A scratch file (since deleted) type-checked
  `example : <deps> → Stmt_X := X_proof` for all 16 proof theorems. The same file checked by `rfl`
  that the short names `Stmt_PF`, `Stmt_L1`, `Stmt_CoeffVanish` and `Stmt_CrudeInt` resolve to
  the pair objects.
* **Framework files.** `Pair/Defs.lean` (252 lines) and `Pair/Statements.lean` (163 lines) have
  0 `sorry` and were not changed in this round. Neither were `Pair/Assembly.lean` or
  `Pair/Main.lean`.
* **Other `sorry`s in the `audit.sh` census.** Nineteen `{7,9,11}` proof files under
  `Zeta2Lean/Proofs/` are **stale stubs from the fork**. These are all of that directory except
  the five reused files. The pair imports none of them. They are why this copy's sibling theorem
  `Zeta2.zeta2_7_9_11_not_all_rational` (`Zeta2Lean/Main.lean`) still shows `sorryAx`. The
  sibling repository has all 24 of its files proved (its `STATUS.md`).
  * To get a clean census, sync those 19 files together with the sibling's `Defs.lean` (two extra
    API lemmas). The pair does not need this.
* **Build warnings in the modules the pair imports.** There are 16:
  * four "declaration uses `sorry`", one for each stub;
  * twelve from Mathlib's style linters: over-long lines (PartialFractions 1, Translation 3,
    Criterion 1, DeltaCalculus 1) and a `show` that changes the goal (DeltaCalculus 6).

  None affects correctness.

### How the files were proved (one line each; details in each file's docstring)

* **GenLinearForm**: linearity (`HasVolkenborn.sum`, `.const_mul`) of the translated `JConv`.
  `(i)₃(i+3) = (i)₄` assembles the translation terms into `genRho0`. `a` stays general, so the file
  is reusable for other families.
* **PartialFractions**: the substitution hom `t ↦ -k₀ + ε` gives `ε⁶ ∣ (Rnum − PFpoly)(−k₀+ε)`.
  The `(X+k)⁶` are pairwise coprime, and a degree count gives `6n+5 < 6n+6` (from `∑h = 0` and
  `n + 2h_m ≥ 0`). The series form multiplies by an inverse. Adapted from the sibling's proof.
* **CoeffVanish**:
  * `rescale (−1)` symmetry `Gser(n−k) = −ρ(Gser k)`, reindexing `u ↦ n−1−u`; the number of
    numerator factors, `6n`, is even;
  * `c₁ = 0` from the coefficient of `t^{6n+5}` in `Stmt_PF.poly`;
  * `c_even = 0` by reflecting the sum.
* **LinearForm**: `Stmt_GenLinearForm` at `a = 6` with `c₁ = c₂ = c₄ = c₆ = 0`.
* **IntegrandTaylor**: closed form of `((c+X)^{d+1})⁻¹` from Mathlib's
  `mk_add_choose_mul_one_sub_pow_eq_one` and `rescale`. Its coefficient 3 is
  `−(i)₃/6 · c^{−(i+3)}`.
* **CrudeIntegrality**:
  * `d`-integral series form a subring, `comap (rescale d)` of `ℤ⟦X⟧`;
  * `2^{6n}` clears the numerator, which has `6n` factors;
  * `(k!(n−k)!)⁶ P_k⁻¹` is a product of geometric series with `c ∣ d_n`;
  * `forms` is proved in `⊥ : Subring ℚ`.
* **Reused files**: copied verbatim from the sibling's proved versions. For how they were proved,
  see the sibling's `STATUS.md`.

## Integrator checks (this round)

* **Diff against `3ba9c24`.** `git diff 3ba9c24` touches only 11 proof files: 6 under
  `Zeta2Lean/Pair/Proofs/` and the 5 reused files under `Zeta2Lean/Proofs/`. These are unchanged:
  * `Pair/Defs`, `Pair/Statements`, `Pair/Assembly`, `Pair/Main`;
  * the sibling framework files `Defs`, `Statements`, `Assembly`, `Main`;
  * `lakefile.toml`, `lake-manifest.json`, `lean-toolchain`.

  No file was added or removed.
* **Theorem headers and imports.** Every `theorem X_proof` header, both hypotheses and type, is
  identical to its stub. Some proofs switched from `:= by` to `where` or term syntax. Imports are
  unchanged.
  * The only new namespace is `Zeta2.Pair.PairPF`, which holds the private helpers of
    PartialFractions. `PF_proof` is outside it.
  * The only new `def`s are private helpers: `crudeIntPS`, `crudeDInt`, `substPS`, `DfnGood` and
    `jcW`. None of them is a `Stmt`.
* **Forbidden and unusual constructs.** None of the 11 changed proof files contains any of:
  `set_option`, `elab`, `macro`, `syntax`, `run_cmd`, `#eval`, `instance`, `attribute`,
  `notation`, `axiom`, `opaque`, `unsafe`, `native_decide`, `implemented_by`, `extern`.
* **Reused files.** The five are byte-identical (`cmp`) to the sibling's proved files. They compile
  against this copy's `Defs.lean`, which lacks only the sibling's unused lemmas `mem_chains` and
  `chainPrev_le`. `Defs.lean` was therefore not synced.
* **Statement issues.** None of the 12 prover reports raised one (five say "none" explicitly), so
  there was nothing to adjudicate and no statement changed. As a regression check, two numerical
  checks were re-run, each with 0 failures:
  * `python3 python/pair_mirror.py --quick` (4 s);
  * `python3 python/pair_audit_independent.py quick` (10 s).
* **Hygiene.** LF line endings verified. The scratch files `Zeta2Lean/Scratch/integrator1_*.lean`
  were deleted.

## Next steps

1. **GAP 4: `Valuation_proof`**, the last routine stub. When it is proved,
   `zeta2_7_9_not_both_rational` depends only on the standard axioms, PNT and the three gap
   hypotheses.
   * All of its hypotheses are proved.
   * The plan is in `Valuation.lean`'s docstring: a Leibniz expansion of the product form, then
     Legendre on the block factorials, then the Δ-calculus. Generalised binomials with a negative
     base need Vandermonde.
   * The valuation track's Theorem G4 (`pair79/valuation`) gives
     `v₂(S) ≥ 12n + 9 − Σ s₂(N_m) − 4λ`.
2. **GAPs 1–3** (growth, denominators, nonvanishing) are research tracks; see `BLUEPRINT_PAIR.md`,
   "The gaps". GAP 1 is the decisive one.
3. **Cosmetic:** silence the style linters (long lines; `show` → `change`).
