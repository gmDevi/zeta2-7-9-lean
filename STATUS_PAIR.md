# Status: at least one of ζ₂(7), ζ₂(9) is irrational (the pair programme)

Updated 2026-09-25, after the cleanup for publication and the Palomar files. The milestones are in the
git log (routine lemmas; GAP 4 valuation; GAP 3 nonvanishing; GAP 1 growth and GAP 2 denominators;
unconditional theorem; publication). Plan and statement map: `BLUEPRINT_PAIR.md`.

## Headline

**The theorem is proved in Lean, with no hypotheses.**

```lean
theorem Zeta2.Pair.zeta2_7_9_not_both_rational_unconditional :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧
      ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q))
-- 'Zeta2.Pair.zeta2_7_9_not_both_rational_unconditional' depends on axioms:
--   [propext, Classical.choice, Quot.sound]
```

(`Zeta2Lean/Pair/Unconditional.lean`; also `pairStatement_unconditional : PairStatement`, and the Palomar
restatement `Zeta2.Pair.zeta2_7_9_not_both_rational_palomar` in `Solution.lean`.)

* All four gaps are closed: GAP 1 (growth), GAP 2 (denominators), GAP 3 (nonvanishing), GAP 4 (valuation).
  Every routine lemma is proved. No file under `Zeta2Lean/` contains `sorry`; the only `sorry` of the
  repository is the intended one in the Palomar statement `Challenge.lean`.
* PNT is not a hypothesis: `Zeta2.PNT_proof : PNT_Stmt` (`Zeta2Lean/Cited/PNT.lean`), Wiener–Ikehara vendored
  from open mathlib4 PRs, copied from the `{7,9,11}` repository.
* `lake build` (default targets `Zeta2Lean`, `Challenge`, `Solution`): green (8966 jobs).
* `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `zeta2_7_9_not_both_rational` (the
  conditional form), `zeta2_7_9_not_both_rational_uncond` (PNT as the only hypothesis), `PNT_proof`,
  `zeta2_7_9_not_both_rational_unconditional`, `pairStatement_unconditional` and
  `zeta2_7_9_not_both_rational_palomar`.
* `scripts/audit.sh`: no `sorry`/`admit` and no forbidden construct anywhere under `Zeta2Lean/`.
* Kernel replay: `bash scripts/kernels.sh Solution` (2026-09-25, after the cleanup): `leanchecker`
  (toolchain `v4.35.0-rc2`) replayed the declarations of all **31 modules** (`Solution` and the 30 project
  modules in the import closure of `Zeta2Lean.Pair.Unconditional`), one module at a time: **all exit 0**
  (`ALL_DONE fail=0`). Slowest: `Pair.Proofs.Denominators` (47 s, 6.8 GB peak RSS, the kernel-reduced
  certificates); every other module 7–10 s at about 6.2 GB (mostly loading Mathlib).
* Palomar: Comparator accepts `Solution.lean` against `Challenge.lean` (next sections).

## What the theorem rests on

1. **Lean kernel + Mathlib** (`v4.35.0-rc2`). Axioms: `propext`, `Classical.choice`, `Quot.sound`.
   No `native_decide`, no `implemented_by`/`extern`, no `axiom` declarations. The certified
   numerics use `decide +kernel` (kernel reduction of `Bool` computations, GAP 2 certificates) and
   `norm_num` on exact rationals (GAP 1 landscape certificates).
2. **Vendored code** (Apache 2.0, headers and authors kept): `Cited/Vendor/PNT/WienerIkehara.lean`
   (the PrimeNumberTheoremAnd contributors, mathlib4 PR #43233/#43238) and
   `Cited/Vendor/PNT/SchwartzCompactSupport.lean` (Terence Tao), byte-identical (SHA-256) to the
   `{7,9,11}` repository's copies; `Cited/PNT.lean` is the PNT part of that repository's `Cited/` tree (its
   `WeakPNT` section is mathlib4 PR #43238). Being Lean proofs, they add no trust.
3. **Trusted definitions in the conclusion** (`Zeta2Lean/Defs.lean`, identical to the `{7,9,11}`
   repository's, and copied verbatim into `Challenge.lean`): `volkenbornSum`, `HasVolkenborn`, `volkenborn`,
   `halfPow`, `J`, `zeta2`. The conclusion is about these objects only; the intermediate objects (`rho0`,
   `Z7`, `Z9`, `integrand`, `ClearsDen`, `configE`) only have to be *some* objects for which the proof goes
   through, and do not need to be trusted.
4. **One cited identification, not formalised:** `zeta2 s := J(s-1)/((s-1) 2^s)` is the
   Kubota–Leopoldt 2-adic zeta value `ζ₂(s)` by LSZ Lemma 2.8 (the same as in the `{7,9,11}` repository).
   Mathlib has no Kubota–Leopoldt `ζ_p` yet. The Lean theorem is literally about the Volkenborn integrals
   `J 6 / 768` and `J 8 / 4096`.

## Per-file census

| file | theorem : Stmt | sorry | lines | status |
|---|---|---|---|---|
| `Pair/Proofs/GenLinearForm` | `GenLinearForm_proof` | 0 | 109 | done |
| `Pair/Proofs/PartialFractions` | `PF_proof` | 0 | 353 | done |
| `Pair/Proofs/CoeffVanish` | `CoeffVanish_proof` | 0 | 280 | done |
| `Pair/Proofs/LinearForm` | `L1_proof` | 0 | 63 | done |
| `Pair/Proofs/IntegrandTaylor` | `IntegrandTaylor_proof` | 0 | 91 | done |
| `Pair/Proofs/CrudeIntegrality` | `CrudeInt_proof` | 0 | 407 | done |
| `Pair/Proofs/NonvanishingLS` | `Nonvanishing_of_LaiSprang` | 0 | 171 | done |
| `Pair/Proofs/Valuation` | `Valuation_proof` (**GAP 4**) | 0 | 826 | done |
| `Pair/Proofs/Nonvanishing` | `Nonvanishing_proof` (**GAP 3**) | 0 | 1557 | done |
| `Pair/Proofs/Growth` | `Growth_proof : Stmt_Growth configE gE` (**GAP 1**) | 0 | 3251 | done |
| `Pair/Proofs/Landscape/Numerics` | certified `log`, `arctan` bounds | 0 | 301 | done |
| `Pair/Proofs/Landscape/RealProfile` | `Preal_le` (`landscape_real`) | 0 | 730 | done |
| `Pair/Proofs/Landscape/VertBase` | helpers for `VertLine` | 0 | 165 | done |
| `Pair/Proofs/Landscape/VertLine` | `Psi_le` (`landscape_vert`) | 0 | 793 | done |
| `Pair/Proofs/Denominators` | `Denominators_proof : Stmt_Denominators configE deltaE` (**GAP 2**) | 0 | 3370 | done |
| `Proofs/JConvergence`, `Translation`, `Criterion`, `DeltaCalculus`, `DeltaFunctions` (reused) | `JConv_proof`, …, `DeltaFun_proof` | 0 | 1060 | done (identical to the `{7,9,11}` repository's) |
| `Cited/PNT` + `Cited/Vendor/PNT/*` | `PNT_proof : PNT_Stmt` | 0 | 1124 | done (copied from the `{7,9,11}` repository) |
| `Defs`, `Statements` (shared) | definitions and statements | 0 | 262 | done (trimmed to what the pair uses) |
| `Pair/Defs`, `Pair/Statements` | definitions and statements | 0 | 421 | done |
| `Pair/Assembly`, `Pair/Main` | `main_of_stmts`, `zeta2_7_9_not_both_rational` (+ variants) | 0 | 310 | done |
| `Pair/Unconditional` | `zeta2_7_9_not_both_rational_unconditional` | 0 | 36 | done |
| `Challenge.lean` / `Solution.lean` | `zeta2_7_9_not_both_rational_palomar` | 1 / 0 | 100 / 28 | the statement (intended `sorry`) / its proof |

### How the gaps were proved (details in each file's docstring)

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
* **GAP 3 (nonvanishing), `Nonvanishing.lean`.** The Lai–Sprang condition at the prime `q = 40m − 1 > 10⁹`
  (Dirichlet: `Nat.frequently_atTop_prime_and_modEq`): `v_q(ρ₀) = −9`, `v_q(Z₇) ≥ −3`, `v_q(Z₉) ≥ −1`
  (docs/proof.md §7, Theorem A, with the parity relation in place of the root trick); then
  `Nonvanishing_of_LaiSprang`.
* **GAP 4 (valuation), `Valuation.lean`.** `v₂(S_n) ≥ 12n − 10⌊log₂ 6n⌋` for every admissible `(n, h)`, by
  the Δ-calculus, Vandermonde's identity and Legendre's formula (docs/proof.md §5, Theorem G4, with a
  uniform logarithmic loss).

## Checks for publication (2026-09-25)

* **Cleanup.** Removed, after checking with `lean --deps` that nothing in the import closure of
  `Zeta2Lean.Pair.Unconditional` uses them: the `{7,9,11}` project's `Zeta2Lean/Main.lean`,
  `Zeta2Lean/Assembly.lean` and 19 stale proof stubs in `Zeta2Lean/Proofs/` (the only `sorry`s of the fork),
  `BLUEPRINT.md`, and that project's Python mirror (`python/mirror.py`, its log, `python/lf_reference.py`).
  The definitions and statements of the `{7,9,11}` construction were removed from `Zeta2Lean/Defs.lean` and
  `Zeta2Lean/Statements.lean`. Docstrings were updated (gaps proved; references to the research session's
  files replaced by `docs/proof.md` sections). The root `Zeta2Lean.lean` imports `Zeta2Lean.Pair.Main` and
  `Zeta2Lean.Pair.Unconditional`, and all 30 remaining modules under `Zeta2Lean/` are in its import closure.
* **Nothing else changed.** For every constant of the 30 project modules in the closure, the hashes of its
  type and value were recorded before and after the cleanup (a Lean script outside the repository): no
  constant changed and none was added; the 92 removed constants are all from `Defs` and `Statements` and
  are all unused by the rest of the closure.
* **Census.** `scripts/audit.sh`: no `sorry`/`admit`, no forbidden construct.
* **Comparator, as Palomar runs it** (the toolchain's `lake comparator`; `Challenge.lean` compiled with bare
  `lean -o` against the toolchain and the Mathlib packages only, under a random alias module; both modules
  exported with `leanexport`; Lean's kernel plus the NanoDa and con-ron kernels): `Your solution is okay!`
  (con-ron accepted 81512 declarations). The run was unsandboxed (no bubblewrap on this machine). Two
  altered copies of `Challenge.lean` were rejected: one with `zeta2 11` in place of `zeta2 9` in the theorem
  ("theorem statement do not match"), and one with `2 ^ (s + 1)` in place of `2 ^ s` in the definition of
  `zeta2` ("Const does not match … 'Zeta2.zeta2'"). leanprover/comparator (commit 32bd61d), built from
  source with the same toolchain and the same kernels, also accepted (unsandboxed).
* **Challenge in isolation.** A copy of `Challenge.lean` outside the project, compiled with bare `lean -o` in
  a clean environment whose `LEAN_PATH` holds only the toolchain and the Mathlib packages: exit 0; its only
  imports are `Init` and `Mathlib`.
* **Metadata.** `formalization.yaml` passes Palomar's own loader (`load_formalization_metadata`,
  `normalized_provenance`: result origin "original"), the upstream v0.4 JSON schema and the classification
  taxonomies; `comparator.json` passes `load_comparator_config`; `LICENSE` is byte-identical to the
  Apache-2.0 text of the Palomar template.
* **Hygiene.** LF line endings. No commit hashes of the local history in any file.

## What remains

Nothing mathematical for the Lean theorem. Optional follow-ups:

1. **Cosmetic:** the style linters (long lines, `show` → `change`, flexible `simp`, unused simp
   arguments) warn in `Growth.lean` and a few reused files. None affects correctness.
2. **LSZ Lemma 2.8** (the identification of `zeta2` with Kubota–Leopoldt `ζ₂`): formalise once
   Mathlib has `ζ_p`.
3. **Palomar:** its official mechanical preflight (the reusable workflow of PalomarSubmission, run on the
   public repository and commit) has not been run for this repository yet.
