# At least one of ζ₂(7), ζ₂(9) is irrational (Lean 4 + Mathlib)

A Lean 4 + Mathlib formalisation of an unrefereed result that our literature search did not find stated
before (see *Novelty* below):

> **Theorem.** At least one of the 2-adic zeta values ζ₂(7), ζ₂(9) is irrational.

It sharpens L. Lai, *On the irrationality of certain 2-adic zeta values*, IJNT 21 (2025) 207–235
(arXiv:2304.00816), Thm 1.1 with s = 3, which proves that at least one of ζ₂(7), ζ₂(9), ζ₂(11), ζ₂(13)
is irrational, and the companion result that at least one of ζ₂(7), ζ₂(9), ζ₂(11) is irrational
(https://github.com/gmDevi/zeta2-7-9-11-lean). Both follow from it.

## What exactly is proved in Lean

```lean
-- Zeta2Lean/Pair/Unconditional.lean
theorem Zeta2.Pair.zeta2_7_9_not_both_rational_unconditional :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧
      ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q))
```

`#print axioms` reports `[propext, Classical.choice, Quot.sound]`, with no hypotheses. There is no `sorry`
(apart from the intended one in the Palomar statement file `Challenge.lean`), no `axiom` declaration and no
`native_decide`; the certificates of the denominator bound are checked by `decide +kernel`, i.e. by kernel
reduction. CI replays every module in the kernel with `leanchecker`. The first conjunct says that the Riemann
sums defining every `J s` converge, so no unspecified value of Mathlib's `limUnder` enters the statement.

The development has two layers:
* `Zeta2Lean/Pair/Main.lean` proves `zeta2_7_9_not_both_rational_uncond (hPNT : PNT_Stmt)`, with the prime
  number theorem as the only hypothesis.
* `Zeta2Lean/Cited/PNT.lean` proves the prime number theorem (`PNT_proof : PNT_Stmt`, i.e. ψ(x)/x → 1 with
  Mathlib's `Chebyshev.psi`) from the Wiener–Ikehara theorem, vendored under `Cited/Vendor/PNT/` from mathlib4 PRs
  #43046, #43233 and #43238 (head 78e1b2bbd0). That code is derived from the PrimeNumberTheoremAnd
  project, keeps its Apache-2.0 headers and authors, and was ported to this Mathlib pin. The vendored files
  are identical to those of the {7,9,11} repository, and `PNT.lean` collects that repository's PNT
  statements and proofs, unchanged, in one file. `Zeta2Lean/Pair/Unconditional.lean` composes the two.

**Trusted definitions.** These are the only project definitions that occur in the statement
(`Zeta2Lean/Defs.lean`, identical to those of the {7,9,11} repository):
* `volkenbornSum f N = (2^N)⁻¹ * ∑_{x < 2^N} f x`, the Riemann sums of the Volkenborn integral on ℤ₂;
* `HasVolkenborn f I`, meaning `Filter.Tendsto (volkenbornSum f) atTop (𝓝 I)` in `ℚ_[2]`;
* `halfPow s x = (x + 1/2)^(-s)`;
* `J s = limUnder …` (the first conjunct of the theorem proves that this limit exists);
* `zeta2 s = J (s-1) / ((s-1) * 2^s)`.

**One cited identification, not formalised.** `zeta2 s` is defined through the Volkenborn integral. By
Lai–Sprang–Zudilin (IMRN 2026, rnag180; arXiv:2505.05005, Lemma 2.8), J(s−1) = (s−1)·2^s·ζ₂(s) for every
integer s ≥ 2, where ζ₂(s) = L₂(s, ω^{1−s}) is the Kubota–Leopoldt value; so `zeta2 s` = ζ₂(s). This
identification is cited, not formalised. It only involves the nonzero rational factor (s−1)·2^s, which does
not affect irrationality. "Rational" in the theorem means "in the image of ℚ → ℚ₂".

## The mathematics

The informal proof is in `docs/proof.md`. The construction is a shifted, well-poised (Rhin–Viola-type)
deformation of the Lai–Sprang–Zudilin family, with sixth powers and a third derivative:

R_n(t) = (2t+n) ∏_{m=1}^{6} (t+½−h_m)_{n+2h_m} / (t)_{n+1}^6,  S_n = ∫_{ℤ₂} R_n'''(t+½) dt = ρ₀ + Z₇ ζ₂(7) + Z₉ ζ₂(9),

in configuration E: 40 | n and h = (n/40)·(−17, 1, 2, 3, 5, 6). The ingredients are:
* the linear form: partial fractions and the translation formula; deg R_n = −5 removes ζ₂(5), and the
  symmetry R_n(−n−t) = −R_n(t) removes the even values;
* the 2-adic size v₂(S_n) ≥ 12n − O(log n) (the Δ-calculus of Sprang and Lai);
* the archimedean size max(|ρ₀|, |Z₇|, |Z₉|) ≤ e^{−0.78n+o(n)}: a contour-integral representation whose
  kernels have poles only at half-integers (possible because R_n has "critical zeros" of order ≥ 5 at the
  half-integers of (−n − n/40, n/40)), and a saddle-point bound with computer-assisted numerical
  inequalities;
* the odd part of a common denominator of ρ₀, Z₇, Z₉ is at most e^{(10 − R)n + o(n)} with R = 1.0901 at
  the "residue level": Legendre-type counts at each pole, the critical zeros to exclude every prime > n, and
  the prime number theorem;
* nonvanishing: for 40 | n with ℓ = n − 1 prime, v_ℓ(ρ₀) = −9 < v_ℓ(Z₇), v_ℓ(Z₉), the ℓ(n)-adic idea of
  Lai and Sprang (arXiv:2306.10393, Lemma 2.2); Dirichlet's theorem gives infinitely many such n;
* Lai's criterion. The margin is 10 − R − 0.78 − 12 log 2 ≈ −0.19 per n; sharper denominator bounds
  (docs/proof.md §4.6, not formalised) give −0.55.

## The proof in Lean

`Zeta2Lean/Pair/Defs.lean` defines the family for any admissible shift vector h : Fin 6 → ℤ, the
partial-fraction coefficients r_{i,k} as Taylor coefficients of G_k(ε) = ε⁶R_n(−k+ε) in `PowerSeries ℚ`, ρ₀,
Z₇ = 46080 c₃, Z₉ = 860160 c₅, configuration E (`configE`: n = 40m, h = m·(−17, 1, 2, 3, 5, 6)) and the
rates `gE = −18/25`, `deltaE = 9`. `Zeta2Lean/Pair/Statements.lean` has one statement per lemma, and
`Zeta2Lean/Pair/Assembly.lean` (`main_of_stmts`) derives the theorem, for any configuration and any rates
g, δ with g + δ < 12 log 2, from the linear form, the 2-adic bound, Lai's criterion and the three "gap"
statements below; `marginE` checks −0.72 + 9 = 8.28 < 12 log 2 = 8.3178. The proofs:
* **Linear form** (`GenLinearForm`, `PartialFractions`, `CoeffVanish`, `LinearForm`): the Riemann sums of
  −R_n'''(x+½) converge to ρ₀ + 60c₃J₆ + 210c₅J₈ = ρ₀ + Z₇ζ₂(7) + Z₉ζ₂(9), with c₁ = c₂ = c₄ = c₆ = 0.
* **2-adic size** (`Valuation.lean`): v₂(S_n) ≥ 12n − 10⌊log₂ 6n⌋ for every admissible (n, h), by the
  Δ-calculus (`Stmt_Delta`, `Stmt_DeltaFun`), Vandermonde's identity and Legendre's formula.
* **Growth** (`Growth.lean`, `Landscape/`): |ρ₀|, |Z₇|, |Z₉| ≤ e^{(−0.72+ε)n} eventually along
  configuration E. Integrals of R_n against the kernels K_s(t) = Σ_ν (t−ν−½)^{−s} (s = 2, 4, 5) on the line
  Re t = n/40 are explicit combinations of ρ₀, c₃, c₅ (Cauchy's theorem, the critical zeros, the symmetry);
  a Cauchy–Schwarz determinant inverts them. Above height 1 the contour is moved to Re t = 0.07n, and
  |R_n(t)| ≤ |2t+n|(|t|+2n)⁶ exp(nΦ(t/n)). Two numerical inequalities for the landscape Φ, on the real
  segment [1/40, 7/100] and on the vertical line through the saddle point, are proved in Lean by
  subdivisions with rational enclosures of log and arctan, each side condition checked by `norm_num`
  (the data were generated by `Landscape/gen/*.py`).
* **Denominators** (`Denominators.lean`): assuming PNT, an explicit common denominator whose odd part is
  ≤ e^{(8.97+ε)n} eventually. Local q-adic bounds come from Legendre-type counts at each pole; the critical
  zeros show that no prime > n divides it; for n/81 < q ≤ n the exponent is bounded through the floor-sum
  function s(n/q), and 766 interval certificates on [1, 41), checked by `decide +kernel` (data from
  `python/pair_den_certs.py`), bound s from below; PNT enters as θ(x)/x → 1; the constant
  T = Σ (10 − σ_i)(1/a_i − 1/b_i) + 12/81 = 8.9607… ≤ 8.97 is checked in fixed-point integer arithmetic by
  the kernel.
* **Nonvanishing** (`Nonvanishing.lean`, `NonvanishingLS.lean`): for q = 40m − 1 prime with
  q > max(B, 10⁹) (infinitely many m by Mathlib's Dirichlet theorem `Nat.frequently_atTop_prime_and_modEq`),
  v_q(ρ₀) = −9, v_q(Z₇) ≥ −3 and v_q(Z₉) ≥ −1; if ζ₂(7) and ζ₂(9) were rational, this would force S_n ≠ 0
  (the argument of Lai–Sprang, Lemma 2.2).
* **Shared infrastructure**, taken unchanged from the {7,9,11} repository: convergence of `J s`, the
  translation formula, Lai's criterion and the Δ-calculus (`Zeta2Lean/Proofs/`, identical files), and the prime
  number theorem (`Zeta2Lean/Cited/`: identical vendored files, and `PNT.lean`, which collects that
  repository's PNT statements and proofs in one file).

**Differences from `docs/proof.md`.** The Lean proof follows the residue-level ("minimal") route of
docs/proof.md §8, with these differences:
* weaker constants: growth rate −0.72 (docs/proof.md: −0.7812 and −0.78127); odd denominators
  e^{8.97n+o(n)} (docs/proof.md: e^{8.9099n+o(n)}; the Lean bound stops the continuum integral at x = 81);
  2-adic loss 10⌊log₂ 6n⌋ (docs/proof.md (5.1): 1 + 10 log₂(1.3n)). The margin 8.28 < 8.3178 still holds;
* its own kernel-checked certificates for the landscape inequalities, in place of the interval-arithmetic
  certification of docs/proof.md §6.4 (Lemma 7), and the kernels K₂, K₄, K₅ in place of (π sec πt)²,
  (π sec πt)⁴ and (π tan πt)'''';
* the prime ℓ = n − 1 > 10⁹ in place of the conditions ℓ ≥ 79, ℓ ≠ 91079 of Theorem A;
* Lai's criterion (`Stmt_Criterion`) applied along configuration E together with the nonvanishing
  statement, instead of Steps 1–3 of §8 along the subsequence I;
* the sign convention S_n = −∫ R_n'''(t+½) dt, which changes the signs of ρ₀, Z₇, Z₉.
The sharper bounds of docs/proof.md (§4.6 and Theorem G′) are not formalised; the theorem does not need them.

## Status and caveats

* **Unrefereed, produced by AI agents.** The mathematics (the construction and the informal proof) and this
  formalisation were produced by AI agents (Anthropic Claude models) under the direction of the maintainer,
  and have not been reviewed by a human expert (`formalization.yaml` describes the process). The Lean kernel
  checks the formal statement as displayed above. Whether that statement matches the mathematics is a matter
  of the trusted definitions and the cited identification listed here.
* **Novelty.** As of 2026-09-24 we found no prior statement of this result, or of the weaker {7, 9, 11}
  result, in refereed work, arXiv (with the forward citations of Lai's paper), Zenodo, zbMATH, OpenAlex,
  Crossref, GitHub or public talks and blogs; a brief re-check on 2026-09-25 found nothing new. Google
  Scholar, MathSciNet and Lai's thesis were not searched, so novelty beyond this search is not established.
  Unrefereed GitHub drafts by C. D. Long (August 2026) claim irrationality of every ζ₂(s) with s odd and
  3 ≤ s ≤ 29, which would imply this result. We have not been able to verify their large-prime step.
* **Relation to the {7, 9, 11} result.** https://github.com/gmDevi/zeta2-7-9-11-lean, registered in the
  Palomar registry as PALOMAR-2026-09-25-000023, proves that at least one of ζ₂(7), ζ₂(9), ζ₂(11) is
  irrational, with the construction 2^{16n}(2t+n)(t+½)_n^8/(t)_{n+1}^8. The theorem here implies it. The
  two proofs share the Volkenborn integral, the Δ-calculus, Lai's criterion and the prime number theorem
  (the shared files above), but not the construction, the denominator argument (Andrews' transformation
  there, Legendre-type counting here) or the nonvanishing argument (a 2-adic dominant term there, an
  auxiliary prime here). This repository started as a copy of that one.
* **Scope.** The theorem says that ζ₂(7) and ζ₂(9) are not both rational. It does not say which of them is
  irrational, and it gives no irrationality measure.

## Layout

* `Zeta2Lean/Defs.lean`, `Zeta2Lean/Statements.lean`: the shared definitions (among them the six trusted
  ones) and the shared statements, taken from the {7,9,11} repository without that project's construction.
* `Zeta2Lean/Proofs/`: proofs of the shared statements, identical to the {7,9,11} repository's files.
* `Zeta2Lean/Cited/PNT.lean`, `Zeta2Lean/Cited/Vendor/PNT/`: the prime number theorem and the vendored
  Wiener–Ikehara code (Apache-2.0).
* `Zeta2Lean/Pair/Defs.lean`, `Zeta2Lean/Pair/Statements.lean`: the construction and one statement per
  lemma. `Zeta2Lean/Pair/Assembly.lean`: the theorem from the statements.
* `Zeta2Lean/Pair/Proofs/*.lean`: one proof per statement. `Landscape/` holds the certified landscape
  inequalities of the growth bound, and `Landscape/gen/` the Python scripts that generated them.
* `Zeta2Lean/Pair/Main.lean`: the wiring, with PNT as the only hypothesis. `Zeta2Lean/Pair/Unconditional.lean`:
  the unconditional theorem and `#print axioms`.
* `BLUEPRINT_PAIR.md`: statement map, dependency graph and design decisions. `STATUS_PAIR.md`: per-file census
  and checks.
* `docs/proof.md`: the informal proof.
* `python/`: `pair_mirror.py` (an exact-arithmetic mirror of the definitions, with numerical checks of every
  statement), `pair_audit_independent.py` (an independent audit engine), `lfam_reference.py` (the exploration
  engine), `pair_den_certs.py` (generator of the denominator certificates), logs of full runs, and
  `zeta2_K17000.json` (2-adic values of the J_s used by the mirrors).
* `scripts/`: `check.sh` (elaborate one file), `build.sh`, `audit.sh` (sorry and forbidden-construct census),
  `kernels.sh` (`leanchecker`, one module at a time).
* `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`: the statement, proof and metadata
  for [Comparator](https://github.com/leanprover/comparator) and the Palomar registry (next section).

## Challenge and Solution

`Challenge.lean` imports only Mathlib. It contains verbatim copies of the six trusted definitions of
`Zeta2Lean/Defs.lean` and states the theorem as `Zeta2.Pair.zeta2_7_9_not_both_rational_palomar`, with
`sorry`. `Solution.lean` proves the same statement from `zeta2_7_9_not_both_rational_unconditional`.
`comparator.json` asks Comparator to check that the two statements, and every definition they use, are
identical, and that the proof uses only `propext`, `Quot.sound` and `Classical.choice`. The toolchain
(v4.35.0-rc2) ships `lake comparator`; it needs `bwrap` (bubblewrap) for its sandbox. On 2026-09-25 the
toolchain's `lake comparator`, run as Palomar runs it (`Challenge.lean` compiled outside Lake against Mathlib
only, both modules exported with `leanexport`, the NanoDa and con-ron kernels besides Lean's), and
leanprover/comparator built from source both accepted `Solution.lean`; both runs were unsandboxed. Two
altered copies of `Challenge.lean` were rejected: one with a changed theorem statement (`zeta2 11` in place
of `zeta2 9`) and one with a changed definition (`2 ^ (s + 1)` in place of `2 ^ s` in `zeta2`).
`formalization.yaml` records the sources, the production process and the review status.

## Building

```bash
lake exe cache get
lake build                                        # also builds Challenge and Solution
lake env lean Zeta2Lean/Pair/Unconditional.lean   # prints the axioms of the unconditional theorem
lake comparator                                   # judges Solution against Challenge (needs bwrap)
bash scripts/audit.sh                             # sorry / forbidden-construct census
bash scripts/kernels.sh                           # leanchecker on every module, one at a time
```

## Licence

Apache-2.0 (`LICENSE`). The vendored files under `Zeta2Lean/Cited/Vendor/PNT/` keep their upstream Apache-2.0
headers and authors.
