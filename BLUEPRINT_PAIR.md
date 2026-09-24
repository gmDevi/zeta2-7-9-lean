# Blueprint: at least one of ζ₂(7), ζ₂(9) is irrational (the PAIR programme)

Lean 4 + Mathlib formalisation plan for the **pair** candidate: the shifted well-poised
(Rhin–Viola-type) deformation of the Lai–Sprang–Zudilin half-shift family, configuration E.
This project is a copy of `zeta2-lean` (the `{7,9,11}` theorem, `BLUEPRINT.md`); the Volkenborn
infrastructure, the criterion and the Δ-calculus are **reused** from it. Everything pair-specific
lives in `Zeta2Lean/Pair/` (namespace `Zeta2.Pair`).

Status (2026-09-24): definitions, statements and the logical assembly are complete, and the build
is green. The main theorem is proved from PNT, the three open gap statements, and routine lemmas.
The routine lemmas are proof stubs (`sorry`) waiting for provers. **The theorem is not proved.**
GAP 1 (growth) is the decisive open problem.

## Main theorem (`Zeta2Lean/Pair/Main.lean`)

```lean
theorem Zeta2.Pair.zeta2_7_9_not_both_rational (hPNT : PNT_Stmt)
    (hGrowth : Stmt_Growth configE gE) (hDen : Stmt_Denominators configE deltaE)
    (hNV : Stmt_Nonvanishing configE) :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧
      ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q))
```

Variants in the same file:
* `zeta2_7_9_not_both_rational_of_gaps`: any `cfg : Config`, any rates `g δ` with
  `g + δ < 12 log 2`. Use it if the gap tracks prove other constants or switch configuration.
* `zeta2_7_9_not_both_rational_LS`: GAP 3 replaced by the arithmetic `Stmt_LaiSprangCond configE`.
* `zeta2_7_9_not_both_rational_uncond (hPNT)`: the gap proof files plugged in. This is the final
  target; its `#print axioms` shows `sorryAx` until every file is proved.

`zeta2 s = J (s-1) / ((s-1) 2^s)`, and `J` is the Volkenborn integral of `(t+1/2)^{-s}`, as in the
sibling (LSZ Lemma 2.8, cited normalisation, see `BLUEPRINT.md`).
`#print axioms` currently shows `propext, sorryAx, Classical.choice, Quot.sound`. The `sorryAx`
comes only from proof stubs.

## The family (`Pair/Defs.lean`)

For `n : ℕ` and `h : Fin 6 → ℤ`:

    R_n(t) = (2t + n) · ∏_{m<6} (t + 1/2 - h_m)_{n+2h_m} / (t)_{n+1}^6,
    (t + 1/2 - h)_{n+2h} = ∏_{u ∈ [-h, n+h)} (t + 1/2 + u)                  (offsets n h)
    S_n = -∫_{ℤ₂} R_n'''(t + 1/2) dt = ρ₀ + 60 c₃ J₆ + 210 c₅ J₈ = ρ₀ + Z₇ ζ₂(7) + Z₉ ζ₂(9).

* `Admissible n h` requires `∑ h = 0`, `n + 2h_m ≥ 0`, and at least 5 = j+2 of the `h_m` are
  `≥ 0`. The last condition is the critical-zero condition that the denominator argument needs.
  Consequences: `deg R_n = -5` (so `c₁ = 0`), `R_n(-t-n) = -R_n(t)` (so `c_even = 0`), and at most
  one negative shift, hence `n + 2h_m ≤ 2n`.
* `r_{6-μ,k} = [ε^μ] G_k(ε)`, where `G_k(ε) = ε^6 R_n(-k+ε)` is computed as an explicit power
  series. `rcoef`, `csum`, `rho0`, `Z7 = 46080 c₃`, `Z9 = 860160 c₅`, `integrand`, `Sn`, `Lform`.
* **Generic linear forms.** `genIntegrand a n r`, `genRho0 a n r` and `genCsum n r` take an
  arbitrary coefficient array and pole order. The pair objects are these at `a = 6`,
  `r = rcoef n h`, so `Stmt_GenLinearForm` does not depend on the family.
* **No power of 2 is built in.** This is unlike the sibling, which uses `2^{16n}`. The
  coefficients have 2-adic denominators of about `2^{12n}`, and `v₂(S_n) ≈ 12n`. Powers of 2 are
  neutral in the criterion, so the assembly bounds the **odd part** `D · ‖D‖₂` of the common
  denominator.
* **Sign convention.** The exploration engine `lfam.py` uses `S = +∫ R'''`. Its
  `(rho0, C[6], C[8])` are therefore `-(ρ₀, Z₇, Z₉)` here, which the mirror checks exactly.
* `Config` is a structure `{n : ℕ → ℕ, h : ℕ → Fin 6 → ℤ, adm, tendsto}`, indexed by the sequence
  index `m`. **`configE`** has `n = 40m` and `h = m·(-17, 1, 2, 3, 5, 6)`, i.e.
  `h/n = (-0.425, 0.025, 0.05, 0.075, 0.125, 0.15)`. Admissibility is proved.
* Target rates: `gE = -18/25 = -0.72` and `deltaE = 9`. `marginE : gE + deltaE < 12 log 2` is
  proved in `Assembly.lean` (8.28 < 8.3178).

## Cited hypotheses

Only `PNT_Stmt` (`ψ(x)/x → 1`, reused from `Zeta2Lean/Statements.lean`). Unlike the sibling, the
pair does **not** assume Andrews' transformation. A gap track that needs it can cite the sibling's
`Andrews_Stmt`.

## Architecture

```
Zeta2Lean/Pair/Defs.lean        definitions (family, coefficients, linear form, Config, configE, targets)
Zeta2Lean/Pair/Statements.lean  one Stmt per lemma; the 3 gap Stmts are parametrised by (cfg, g/δ)
Zeta2Lean/Pair/Assembly.lean    main_of_stmts (complete; generic in cfg, g, δ), marginE, bound_core, ...
Zeta2Lean/Pair/Proofs/*.lean    theorem X_proof (deps as hypotheses) : Stmt_X := by sorry   (11 files)
Zeta2Lean/Pair/Main.lean        wiring + 4 variants of the main theorem + #print axioms
python/pair_mirror.py           exact mirror of Pair/Defs.lean + numerical check of every Stmt
python/lfam_reference.py        verbatim copy of the exploration engine lfam.py (independent cross-check)
```

Proof files import only `Zeta2Lean.Pair.Statements`, which imports `Zeta2Lean.Statements`. They
receive their dependencies as hypotheses and can be elaborated independently with
`scripts/check.sh`.

## Statement map

| Stmt | content | file | deps | gap | diff. |
|---|---|---|---|---|---|
| `Stmt_GenLinearForm` | Riemann sums of `∑ (i)₃ r_{i,k}(x+k+½)^{-i-3}` → `genRho0 + ∑ (i)₃ c_i J_{i+3}` (any `a`, `r`) | `GenLinearForm` | JConv, Translation (sibling) | '' | 2 |
| `Stmt_PF` | `Rnum = PFpoly`; Taylor form at non-poles | `PartialFractions` | – | '' | 4 |
| `Stmt_CoeffVanish` | `r_{i,n-k} = (-1)^{i+1} r_{i,k}`, `c₁ = 0`, `c_even = 0` | `CoeffVanish` | PF | '' | 3 |
| `Stmt_L1` | `S_n = ρ₀ + 60c₃J₆ + 210c₅J₈` (only ζ₂(7), ζ₂(9)) | `LinearForm` | GenLinearForm, CoeffVanish | '' | 2 |
| `Stmt_IntegrandTaylor` | `integrand n h x = -6 [ε³] R_n(x+½+ε)` (product form) | `IntegrandTaylor` | PF | '' | 2 |
| `Stmt_CrudeInt` | `2^{6n}(k!(n-k)!)^6 d_n^{6-i} r_{i,k} ∈ ℤ`; `Dcrude n = 2^{6n} n!^6 d_{2n}^{10}` clears ρ₀, Z₇, Z₉ | `CrudeIntegrality` | – | '' | 3 |
| `Stmt_Valuation` | **GAP 4**: `‖S_n‖ 2^{12n} ≤ c (n+1)^A`, all admissible `(n,h)` | `Valuation` | IntegrandTaylor, Delta, DeltaFun (sibling) | valuation (expected routine) | 4 |
| `Stmt_LaiSprangCond cfg` | ∀B, frequently ∃ prime q > B: `v_q ρ₀ < v_q Z₇, v_q Z₉` | (hypothesis of the `_LS` variant) | – | nonvanishing (alternative) | 5 |
| `Nonvanishing_of_LaiSprang` | `Stmt_LaiSprangCond cfg → Stmt_Nonvanishing cfg` | `NonvanishingLS` | L1 | '' | 2 |
| `Stmt_Growth cfg g` | **GAP 1**: ∀ε>0, eventually `|ρ₀|,|Z₇|,|Z₉| ≤ e^{(g+ε)n}` | `Growth` (target `configE`, `gE`) | PF, CoeffVanish | growth | 5 |
| `Stmt_Denominators cfg δ` | **GAP 2**: PNT → ∃D, eventually ClearsDen, `D‖D‖₂ ≤ e^{(δ+ε)n}` | `Denominators` (target `configE`, `deltaE`) | PF, CoeffVanish, CrudeInt | denominators | 5 |
| `Stmt_Nonvanishing cfg` | **GAP 3**: ζ₂(7), ζ₂(9) rational → frequently `S_n ≠ 0` | `Nonvanishing` (target `configE`) | L1, IntegrandTaylor, Delta, DeltaFun | nonvanishing | 5 |
| `PairStatement` | main theorem | `Assembly.lean` (done) | JConv, L1, Valuation, Criterion, 3 gaps, PNT | – | – |

Reused sibling statements and their proof files, which the pair `Main.lean` imports:
`Stmt_JConv` (`Proofs/JConvergence`), `Stmt_Translation` (`Proofs/Translation`),
`Stmt_Criterion` (`Proofs/Criterion`), `Stmt_Delta` (`Proofs/DeltaCalculus`),
`Stmt_DeltaFun` (`Proofs/DeltaFunctions`). **These files are copies. When the sibling project
proves them, copy the proved versions into this project** (same paths, same statements). No
other sibling proof file is used.

## Dependency graph

```
                      PairStatement (Assembly.lean, done; generic in cfg, g, δ)
   ┌────────┬─────────┬──────────┬───────────┬──────────────┬────────────────┬─────────┐
 JConv     L1     Valuation   Criterion   Growth(GAP1)  Denominators(GAP2)  Nonvanishing(GAP3)  PNT
  (sib)   /   \     /   |  \     (sib)                                         ▲
 GenLinearForm CoeffVanish  IntegrandTaylor Delta DeltaFun           NonvanishingLS ← LaiSprangCond
  /     \        |              |       (sib)  (sib)                 (← L1)
 JConv Translation PF           PF
```

The leaves are PF, CrudeInt, GenLinearForm (from sibling leaves), the gap files and the sibling
files. Every file can be worked on in parallel.

## The assembly (`Pair/Assembly.lean`, proved)

Suppose `ζ₂(7) = q₇` and `ζ₂(9) = q₉` are rational.

1. Integers `a_m = num(D_m·(ρ₀, Z₇, Z₉))` equal `D_m·(ρ₀, Z₇, Z₉)` eventually (GAP 2). No choice
   is needed.
2. `B_m := ∑|a_{m,j}|` bounds every coefficient trivially.
3. `L_m = D_m · S_n ≠ 0` frequently, by GAP 3 and L1.
4. Eventually `B_m ‖L_m‖₂ ≤ 3c (n+1)^A e^{-(12 log 2 - g - δ - 2ε) n}`, with
   `ε = (12 log 2 - g - δ)/4`, by GAPs 1, 2, 4 (`bound_core`). This tends to `0` because
   `cfg.n m → ∞`.
5. Lai's criterion (sibling `Stmt_Criterion`) gives the contradiction.

## The gaps: exact form, targets, status

All three are hypotheses of the main theorem and are stated for a general configuration and
general rates.

**GAP 1: growth.** `Stmt_Growth configE gE`, target `g = -0.72`.
* Any `g` with `g + δ < 8.3178` works. With the residue-level `δ ≈ 8.91` one needs `g < -0.59`.
* Measured `raw/n`: -0.769 (n=40), -0.818 (80), -0.827 (120), -0.820 (200), -0.807 (400),
  -0.797 (800). Fits give about -0.786.
* The naive residue bound is +0.77.
* **New conjecture (architect):** `g_E = -0.78128`. This is the value
  `Re[φ(τ*) + 2πiτ*]` of the Stirling phase
  `φ(τ) = ∑_m [F(τ+1+η_m) − F(τ−η_m)] − 6[F(τ+1) − F(τ)]`, with `F(z) = z log z − z`, at the
  complex point `τ* = 0.069590 + 0.031280i`, where `φ'(τ*) = -2πi`.
* Recipe: take the maximum over the points to the right of the pole interval where
  `e^{φ'} = 1`, the roots of a degree-9 polynomial.
* The same recipe gives `-1.1808` for the `{7,9,11}` configuration D (measured -1.22 at n=650,
  rising).
* The `2πiτ` term points to a contour-integral proof with an `e^{±2πit}` kernel
  (`Growth.lean`; scratchpad `pair79/architect/saddle_growth.py`).

**GAP 2: denominators.** `Stmt_Denominators configE deltaE` (assuming PNT), target `δ = 9`.
* The statement bounds the odd part, so the 2-part of `D` is free: take it from `Dcrude`.
* Do **not** state `odd part ∣ d_n^9`. The verifier found exponent `11 = a+j+2` at many primes
  `q > √n`.
* Plan: Zudilin's derivative lemma gives `v_q(r_{i,k}) ≥ v_q(G_k(0)) − (6−i)` for `q² > 3n+1`.
  Legendre gives `s_res(q)`. The critical-zero switch removes the primes in `(n, 2n)`. Small
  primes contribute `O(√n)`. PNT then gives `log(odd D_n)/n → 10 − R_∞ ≈ 8.91`, with
  `R_∞ = ∫_1^∞ s(x)dx/x² ≈ 1.09`.
* Observed true values: 8.37 (n=200), 8.32 (400).

**GAP 3: nonvanishing.** `Stmt_Nonvanishing configE`.
* The statement is conditional on rationality, which is all the criterion needs. An
  unconditional proof also works.
* `S_n ≠ 0` at every tested `n ≤ 800`.
* **Recommended route:** prove `Stmt_LaiSprangCond configE` (pure arithmetic about ρ₀, Z₇, Z₉),
  then apply `Nonvanishing_of_LaiSprang`. At `n = 120, 200, 400`, *every* prime `q ∈ (√n, n]`
  satisfies it, with `v_q Z₇ − v_q ρ₀ ≥ 7`, `v_q Z₉ − v_q ρ₀ ≥ 9` and `v_q ρ₀ ∈ [−11, −5]`
  (scratchpad `pair79/architect/laisprang_check.out`).
* Alternatives: Lai's dominant term along a subsequence, or a Casoratian.

**GAP 4: valuation.** `Stmt_Valuation`. This is a proof obligation, not a hypothesis.
* It is expected to be routine: the L3 argument of proof.md §5 with shifted runs.
* Pitfall: generalised binomials `C(x + a, L)` with `a < 0` for small `x`. Use Vandermonde and
  `Stmt_DeltaFun.binom` with `j = 0`; see `Valuation.lean`.
* Measured `12n − v₂(S_n)` is 23…39.

## Numerical mirror (`python/pair_mirror.py`)

Pure standard library. Run `python3 python/pair_mirror.py [--quick]`: about 10 s quick, 45 s full.
It uses `python/zeta2_K17000.json` for the J-values and, optionally, `python/lfam_reference.py`.
It transcribes every definition literally (`offsets` = `Ico(-h, n+h)`, `rcoef` = 0 outside the
range) and checks:

* `rho0`, `Z7`, `Z9` and all `c_i` against the independent engine `lfam_reference.py`. They agree
  exactly on 31 cases (random admissible `h`, `n ≤ 12`, and config E at `n = 40`, plus 80 in the
  full run). The only live zeta values are ζ₂(7) and ζ₂(9).
* `Stmt_PF` (`poly` for n ≤ 5, `series` at random `y`), `Stmt_CoeffVanish`,
  `Stmt_CrudeInt` (`coef`, `forms`) and `Stmt_IntegrandTaylor`.
* `Stmt_GenLinearForm` / `Stmt_L1`: 2-adic convergence of the Riemann sums of the Lean integrand
  to `ρ₀ + 60c₃J₆ + 210c₅J₈`.
* `Stmt_Valuation`: `max (12n − v₂S)/log₂(n+1) = 5.7` on all tested cases. The quick run covers
  config E at n = 40, 80, 120; the full run adds n = 160.
* GAP data for E (n = 40…160, plus lfam at 200 and 400):
  * growth `raw/n`;
  * log of the odd denominator per `n`;
  * maximal prime exponent 11;
  * `v₂S − 12n`;
  * the criterion quantity `log(B‖L‖₂)/n`: -1.50, -1.05, -0.99, -0.89, -0.64, -0.74;
  * no prime `> n`;
  * `S_n ≠ 0`.
  These reproduce the verifier's `v₂(S₂₀₀) = 2365` and `v₂(S₄₀₀) = 4763`.
* `Stmt_LaiSprangCond` at every prime `q ∈ (√n, n]`, the GAP 1 saddle-point values, and
  `marginE`.

The full-run log is in the scratchpad (`pair79/architect/pair_mirror_full.log`); 0 checks fail.

## Design decisions

1. **Gap statements are abstract and parametric.** The denominators are "some `D` with a bound
   on its odd part", not a `d_n^{a+j}` formula. The rates `g` and `δ` and the configuration are
   parameters, so a gap track can prove whatever constants it reaches without touching the
   assembly. The margin condition `g + δ < 12 log 2` is the only coupling.
2. **Weakest forms.** GAP 2 integrality is only *eventual*. GAP 3 is *conditional* on
   rationality, which allows the Lai–Sprang route. GAP 3 and GAP 4 are stated for *every* limit
   `I` of the Riemann sums, so they need no convergence proof.
3. **No choice in the assembly.** The integer sequences are numerators of `D·ρ₀` etc.
   `B := ∑|a_j|` makes the coefficient bounds of the criterion trivial for all `m`.
4. **Generic linear form.** It is proved once for any `(a, r)`, so it is reusable for other
   configurations or families (`a = 8` for a shifted `{7,9,11}`).
5. **Shift vector as data.** `h : Fin 6 → ℤ` per degree, with configurations indexed by `m`.
   There is no division `n/40` anywhere. A new configuration needs a `Config` value and new gap
   proofs; the assembly and routine lemmas are unchanged.
6. **Unnormalised family.** This matches all exploration data. The 2-part is handled by
   `‖D‖₂` (see "The family").

## Changes to the copied infrastructure

* `Zeta2Lean.lean` (library root) now also imports `Zeta2Lean.Pair.Main`, so plain `lake build`
  builds both theorems.
* `README.md` has a pair paragraph.
* `python/lfam_reference.py` was added: a verbatim copy of `lfam.py`, converted to LF line
  endings.
* No change to `Zeta2Lean/Defs.lean`, `Statements.lean`, `Assembly.lean`, `Main.lean` or
  `Proofs/*`.

## Workflow for provers

* Elaborate one file:
  `wsl -d Ubuntu --cd /home/mdevi/zeta2-pair-lean -- bash scripts/check.sh Zeta2Lean/Pair/Proofs/Foo.lean`.
* Build: `scripts/build.sh Zeta2Lean.Pair.Main`. Census: `scripts/audit.sh`.
* Never edit `Pair/Defs.lean` or `Pair/Statements.lean`. If a statement looks wrong or
  unprovable, report it to the architect with a counterexample from `pair_mirror.py`.
* Work in `namespace Zeta2.Pair`, where short names refer to the pair objects. Put helper lemmas
  in your own file with distinctive names; `private` is recommended.
* Scratch work goes in `Zeta2Lean/Scratch/<yourname>_*.lean`. Delete it when done.
* Gap tracks may add intermediate `Stmt`s in their own files. Ask the architect before changing
  a gap statement.
