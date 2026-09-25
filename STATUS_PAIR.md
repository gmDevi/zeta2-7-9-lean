# Status: at least one of ζ₂(7), ζ₂(9) is irrational (the pair programme)

Updated 2026-09-25 by the integrator after the gap round (GAP 1 growth, GAP 2 denominators).
Earlier milestones: `a0c8815` (routine lemmas), `7849511` (GAP 4 valuation), `80b7ece` (GAP 3
nonvanishing), `5dde6c8` (GAP 1 work in progress). Plan and statement map: `BLUEPRINT_PAIR.md`.

## Headline

**The theorem is proved in Lean, with no hypotheses.**

```lean
theorem Zeta2.Pair.zeta2_7_9_not_both_rational_unconditional :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧
      ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q))
-- 'Zeta2.Pair.zeta2_7_9_not_both_rational_unconditional' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

(`Zeta2Lean/Pair/Unconditional.lean`; also `pairStatement_unconditional : PairStatement`.)

* All four gaps are closed: GAP 1 (growth), GAP 2 (denominators), GAP 3 (nonvanishing),
  GAP 4 (valuation). Every routine lemma is proved. The pair has **0 `sorry`**.
* PNT is no longer a hypothesis: `Zeta2.PNT_proof : PNT_Stmt` (`Zeta2Lean/Cited/PNT.lean`),
  Wiener–Ikehara vendored from open mathlib4 PRs, copied from the sibling `{7,9,11}` project.
* `bash scripts/build.sh Zeta2Lean.Pair.Unconditional`: green (8960 jobs, exit 0).
  `bash scripts/build.sh Zeta2Lean.Pair.Main`: green (8956 jobs).
* `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for all of
  `zeta2_7_9_not_both_rational` (the frozen conditional form), `zeta2_7_9_not_both_rational_uncond`
  (PNT as the only hypothesis), `PNT_proof`, `zeta2_7_9_not_both_rational_unconditional` and
  `pairStatement_unconditional`.
* `scripts/audit.sh`: no forbidden construct anywhere; no `sorry` in any file the pair imports
  (the 19 remaining `sorry`s are the stale `{7,9,11}` stubs of the fork, see below).
* Kernel replay: `leanchecker` on all 30 project modules in the import closure of
  `Zeta2Lean.Pair.Unconditional`, one at a time: all pass (see "Kernel replay" below).

## What the theorem rests on

1. **Lean kernel + Mathlib** (`v4.35.0-rc2`). Axioms: `propext`, `Classical.choice`, `Quot.sound`.
   No `native_decide`, no `implemented_by`/`extern`, no `axiom` declarations. The certified
   numerics use `decide +kernel` (kernel reduction of `Bool` computations, GAP 2 certificates) and
   `norm_num` on exact rationals (GAP 1 landscape certificates).
2. **Vendored code** (Apache 2.0, headers and authors kept): `Cited/Vendor/PNT/WienerIkehara.lean`
   (the PrimeNumberTheoremAnd contributors, mathlib4 PR #43233/#43238) and
   `Cited/Vendor/PNT/SchwartzCompactSupport.lean` (Terence Tao), byte-identical (SHA-256) to the
   sibling's copies; `Cited/PNT.lean` is the PNT part of the sibling's `Cited/` tree (its
   `WeakPNT` section is mathlib4 PR #43238). Being Lean proofs, they add no trust.
3. **Trusted definitions in the conclusion** (sibling `Defs.lean`): `volkenbornSum`,
   `HasVolkenborn`, `halfPow`, `J`, `zeta2`. The conclusion is about these objects only; the
   intermediate objects (`rho0`, `Z7`, `Z9`, `integrand`, `ClearsDen`, `configE`) only have to be
   *some* objects for which the proof goes through, and do not need to be trusted.
4. **One cited identification, not formalised:** `zeta2 s := J(s-1)/((s-1) 2^s)` is the
   Kubota–Leopoldt 2-adic zeta value `ζ₂(s)` by LSZ Lemma 2.8 (the same as in the sibling; see its
   `STATUS.md`). Mathlib has no Kubota–Leopoldt `ζ_p` yet. The Lean theorem is literally about
   the Volkenborn integrals `J 6 / 768` and `J 8 / 4096`.

## Per-file census (`Zeta2Lean/Pair/`, reused and vendored files)

| file | theorem : Stmt | sorry | lines | status |
|---|---|---|---|---|
| `Pair/Proofs/GenLinearForm` | `GenLinearForm_proof` | 0 | 109 | done |
| `Pair/Proofs/PartialFractions` | `PF_proof` | 0 | 353 | done |
| `Pair/Proofs/CoeffVanish` | `CoeffVanish_proof` | 0 | 279 | done |
| `Pair/Proofs/LinearForm` | `L1_proof` | 0 | 63 | done |
| `Pair/Proofs/IntegrandTaylor` | `IntegrandTaylor_proof` | 0 | 91 | done |
| `Pair/Proofs/CrudeIntegrality` | `CrudeInt_proof` | 0 | 407 | done |
| `Pair/Proofs/NonvanishingLS` | `Nonvanishing_of_LaiSprang` | 0 | 171 | done |
| `Pair/Proofs/Valuation` | `Valuation_proof` (**GAP 4**) | 0 | 826 | done (`7849511`) |
| `Pair/Proofs/Nonvanishing` | `Nonvanishing_proof` (**GAP 3**) | 0 | 1557 | done (`80b7ece`) |
| `Pair/Proofs/Growth` | `Growth_proof : Stmt_Growth configE gE` (**GAP 1**) | 0 | 3251 | done (this round) |
| `Pair/Proofs/Landscape/Numerics` | certified `log`, `arctan` bounds | 0 | 301 | done (this round) |
| `Pair/Proofs/Landscape/RealProfile` | `Preal_le` (`landscape_real`) | 0 | 730 | done (this round) |
| `Pair/Proofs/Landscape/VertBase` | helpers for `VertLine` | 0 | 165 | done (this round) |
| `Pair/Proofs/Landscape/VertLine` | `Psi_le` (`landscape_vert`) | 0 | 793 | done (this round) |
| `Pair/Proofs/Denominators` | `Denominators_proof : Stmt_Denominators configE deltaE` (**GAP 2**) | 0 | 3370 | done (this round) |
| `Proofs/JConvergence`, `Translation`, `Criterion`, `DeltaCalculus`, `DeltaFunctions` (reused) | `JConv_proof`, …, `DeltaFun_proof` | 0 | 1060 | done (synced from sibling) |
| `Cited/PNT` + `Cited/Vendor/PNT/*` (new) | `PNT_proof : PNT_Stmt` | 0 | 1123 | done (copied from sibling) |
| `Pair/Assembly`, `Pair/Main` (frozen) | `main_of_stmts`, `zeta2_7_9_not_both_rational` (+ variants) | 0 | 307 | done |
| `Pair/Unconditional` (new) | `zeta2_7_9_not_both_rational_unconditional` | 0 | 35 | done (this round) |

### How the two gaps of this round were proved (details in each file's docstring)

* **GAP 1 (growth), `Growth.lean` + `Landscape/`.** Target rate `gE = -0.72` (true rate
  `-0.78127`). Contour-integral representation with half-integer kernels
  `K_s(t) = ∑_ν (t - ν - 1/2)^{-s}`: on the line `Re t = n/40` the kernel integrals `I₂, I₄, I₅`
  are explicit combinations of `ρ₀, Z₇, Z₉` (Cauchy on half-planes, the five critical zeros, the
  symmetry `R_n(-n-t) = -R_n(t)`), inverted via a Cauchy–Schwarz determinant. The contour is
  shifted to `Re t = 0.07 n` above height 1 and each piece is bounded by the pointwise bound
  `|R_n(t)| ≤ poly · exp(n Φ(t/n))`. The two numerical landscape inequalities
  (`Φ(ξ,0) ≤ -18/25` on `[1/40, 7/100]`; `Φ(7/100, η) - 2πη ≤ -18/25` on `(0,1]`) are kernel-checked
  certified subdivisions with rational `log`/`arctan` enclosures, generated by
  `Landscape/gen/*.py` (exact fractions).
* **GAP 2 (denominators), `Denominators.lean`.** Target `deltaE = 9` for the odd part. Residue
  level only (no second/third-order savings): a local `q`-adic bound for every odd prime
  (Legendre-type counts, capped valuations; primes `q > n` do not divide, by absorption into the
  critical zeros), 766 kernel-checked interval certificates for the residue function
  `s(x) = min_y Vl(x, y)` on `[1, 41)` (data from `python/pair_den_certs.py`), and PNT through
  `θ(x)/x → 1`. The resulting constant is `T = 8.9607… ≤ 8.97 < 9` (`margin_T`, fixed-point
  integer arithmetic in the kernel). With `gE + deltaE = 8.28 < 12 log 2 = 8.3178` this closes the
  criterion.

## Integrator checks (this round)

* **Frozen files untouched.** `git diff` against `5dde6c8` touches only `Pair/Proofs/Growth.lean`
  and `Pair/Proofs/Denominators.lean` among existing Lean files; `Pair/Defs`, `Pair/Statements`,
  `Pair/Assembly`, `Pair/Main`, the sibling framework files, `lakefile.toml`,
  `lake-manifest.json` and `lean-toolchain` are unchanged. The theorem headers of `Growth_proof`
  and `Denominators_proof` are identical to their stubs.
* **New files:** `Pair/Proofs/Landscape/{Numerics,RealProfile,VertBase,VertLine}.lean` and
  `Landscape/gen/*.py` (GAP 1), `python/pair_den_certs.py` (GAP 2), `Cited/PNT.lean`,
  `Cited/Vendor/PNT/{LICENSE,SchwartzCompactSupport.lean,WienerIkehara.lean}`,
  `Pair/Unconditional.lean`, `scripts/kernels.sh`. The root `Zeta2Lean.lean` now also imports
  `Zeta2Lean.Pair.Unconditional`.
* **Statement issues.** Neither prover raised one. Regression: `python3 python/pair_mirror.py
  --quick` (0 checks failed) and `python3 python/pair_audit_independent.py quick` (0 failures).
* **Hygiene.** LF line endings. The provers' scratch files (`Zeta2Lean/Scratch/`, 26 files, never
  committed) were moved out of the repository to `C:\tmp\pair79_round1_scratch`.
* **Other `sorry`s in the `audit.sh` census.** Nineteen `{7,9,11}` proof files under
  `Zeta2Lean/Proofs/` are stale stubs from the fork (all of that directory except the five reused
  files). The pair imports none of them; they only make this copy's `Zeta2Lean/Main.lean`
  (`zeta2_7_9_11_not_all_rational`) show `sorryAx`. The sibling repository has that theorem fully
  proved.

## Kernel replay

`bash scripts/kernels.sh` (2026-09-25): `leanchecker` (toolchain `v4.35.0-rc2`) replayed the own
declarations of all **30 project modules** in the import closure of
`Zeta2Lean.Pair.Unconditional`, one module at a time: **all exit 0** (`ALL_DONE fail=0`). These are
the 20 `Pair` modules (incl. `Landscape/*` and `Unconditional`), `Cited/PNT` and the two vendored
PNT files, the five reused `Proofs/*` files, and `Defs`/`Statements`. Slowest:
`Pair.Proofs.Denominators` (121 s, 6.8 GB peak RSS, the kernel-reduced certificates); every other
module 11–43 s at about 6.2 GB (mostly loading Mathlib).

## What remains

Nothing mathematical for the Lean theorem. Optional follow-ups:

1. **Cosmetic:** the style linters (long lines, `show` → `change`, flexible `simp`, unused simp
   arguments) warn in `Growth.lean` and a few reused files. None affects correctness.
2. **Census cleanliness:** sync the 19 stale `{7,9,11}` files and the sibling's `Defs.lean` (two
   extra API lemmas), or delete the `{7,9,11}` tree from this copy.
3. **Documentation:** the body of `BLUEPRINT_PAIR.md` (now with a status note at the top) and the
   frozen docstring of `Pair/Main.lean` still describe the gaps as open; the docstrings of the gap
   files and this file are authoritative.
4. **LSZ Lemma 2.8** (the identification of `zeta2` with Kubota–Leopoldt `ζ₂`): formalise once
   Mathlib has `ζ_p`.
