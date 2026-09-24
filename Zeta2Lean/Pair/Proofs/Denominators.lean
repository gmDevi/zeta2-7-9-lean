import Zeta2Lean.Pair.Statements

/-!
# GAP 2 (denominators): a provable common denominator with small odd part

gap: 'denominators' (open; hypothesis of the main theorem).

**Task.** Prove `Stmt_Denominators configE deltaE`: assuming PNT, construct `D : ℕ → ℕ` with
`ClearsDen (D m) (40m) (m · hE)` eventually and, for every `ε > 0`, eventually
`D m · ‖D m‖₂ ≤ exp((9 + ε) · 40m)`.  `D m · ‖D m‖₂` is the **odd part** of `D m`: the power of `2`
is free (it cancels against `‖D S‖₂` in the criterion), so take e.g. the full 2-part of
`Dcrude n = 2^{6n} n!^6 d_{2n}^{10}` (`Stmt_CrudeInt.forms` clears every 2-adic denominator).
Any `δ` with `g + δ < 12 log 2` works with a growth rate `g` (`Pair/Main.lean`); with the
conjectured `g = -0.781` one needs `δ < 9.099`.

**Warning (verifier correction).** Do **not** aim for `odd part ∣ d_n^{a+j} = d_n^9`: for
configuration E many primes `q > √n` occur in the denominator of `ρ₀` with exponent
`11 = a + j + 2` (5 primes at `n = 120`, 15 at `n = 400`, 23 at `n = 560`).  Lai's Lemmas 4.1/4.3
(products of simple-pole factors with integral residues) do not apply verbatim to factors with
`h < 0`.

**Numerical status** (`python/pair_mirror.py`, "GAP data"): `log(odd part of the true common
denominator)/n = 7.18, 7.86, 8.00, 8.12, 8.37, 8.32` at `n = 40, 80, 120, 160, 200, 400`; no prime
`> n` ever occurs; for primes `q ∈ (√n, n]`: `v_q(ρ₀) ∈ [-11, -4]` (`-4` occurs at `n = 160`),
`v_q(Z₇) ≥ -4`, `v_q(Z₉) ≥ -2` (`scratchpad/pair79/architect/laisprang_check.out`, `n = 120,
200, 400`; audit `python/pair_audit_independent.py`, `n = 40, 80, 120, 160`).  Residue-level
provable estimate: `δ = 10 - R_∞ ≈ 8.91`, `R_∞ = ∫_1^∞ s(x) dx/x² ≈ 1.09` (verifier's `rinf.py`,
deterministic).

**Proof plan (the verifier's sketch, completed).**  Fix an odd prime `q`.
1. *Derivative lemma* (Zudilin 2004 Lemma 17; proof.md §4.3 Step 6).  Every linear factor of
   `G_k(ε)` is `α (1 + ε/α)` with `2α ∈ ℤ ∖ {0}`, `|2α| ≤ 3n + 1` (numerator `u - k + 1/2`,
   `u ∈ [-h_m, n + h_m)`, `h_m ≤ n/2`; denominator `j - k`; the factor `n - 2k + 2ε` — if `n = 2k`
   it is `2ε` and is treated separately).  If `q² > 3n + 1` then `v_q(α) ≤ 1`, so
   `log(G_k(ε)/G_k(0)) = ∑_μ L_μ ε^μ` with `v_q(L_μ) ≥ -μ`, and (`μ ≤ 5 < q`)
   `v_q(r_{i,k}) ≥ v_q(G_k(0)) - (6 - i)`.
2. *Residue valuation* (Legendre, `predict.py: residue_vals`).  `G_k(0) = (n - 2k) ∏_m P_m(k) /
   (k! (n-k)!)^6`, `P_m(k) = ∏_{u ∈ [-h_m, n+h_m)} (u - k + 1/2)` (runs of consecutive odd numbers
   over `2`).  `s_res(q) := min_k v_q(G_k(0))` is a floor-function expression in `n/q`, `h_m/q`; it
   can be `-1` (whence exponent 11).  Generally `v_q(G_k(0)) ≥ -6 · #{j ≥ 1 : q^j ≤ 3n+1}` (each
   level `j` loses at most 6: runs of total length `6n` versus `6(⌊k/q^j⌋ + ⌊(n-k)/q^j⌋)`).
3. *Assembling `ρ₀`, `Z`.*  `A_k^{(s)}` has `v_q ≥ -s` when `q² > 2n`, so
   `v_q(ρ₀) ≥ s_res(q) - 10`, `v_q(c_i) ≥ s_res(q) - (6 - i)` (`Z₇`: `-3`, `Z₉`: `-1` shifts).
4. *Primes `q ∈ (n, 2n)`: the critical-zero switch* (Lai Lemma 4.6 / proof.md §4.2).  For
   `X(k,ℓ) = ∑_i (i)₄ r_{i,k} (ℓ + 1/2)^{-(i+4)}`, the point `t₀ = ℓ - k + 1/2 = -1/2 - (k - ℓ - 1)`
   is a zero of `R_n` of order `≥ 5` (five non-negative shifts ⇒ every offset in `[0, n)` occurs
   five times), so `R_n^{(4)}(t₀) = 0` and
   `X(k, ℓ) = -∑_{k' ≠ k} ∑_i (i)₄ r_{i,k'} (ℓ - k + k' + 1/2)^{-(i+4)}`;
   if `q ∣ 2ℓ + 1` then `q ∤ 2(ℓ - k + k') + 1` (`0 < |k' - k| ≤ n < q`).  Hence no prime `> n`.
5. *Small primes* `q ≤ √(3n+1)`: exponent `O(log n / log q)` from 1–3 ⇒ total `O(√n)` (Chebyshev
   bounds suffice).
6. *Asymptotics (PNT).*  With
   `D_n = 2^{e_n} ∏_{q ≤ √(3n+1)} q^{O(log_q n)} ∏_{√(3n+1) < q ≤ n} q^{10 - s_res(q)}`:
   `log(odd part) = 10 θ(n) - ∑_{q} s_res(q) log q + O(√n log n)`, and since `s_res(q) = s(n/q)`
   for a piecewise-constant `s` (floor functions; configuration E scales with `n`), PNT gives
   `∑_{q ≤ n} s(n/q) log q = n ∫_1^∞ s(x) dx/x² + o(n)` (Riemann–Stieltjes with `θ(x) ~ x`), i.e.
   `log(odd part)/n → 10 - R_∞ ≈ 8.91 < 9`.
Suggested file split: define `D` and prove integrality prime by prime (steps 1–5), then a separate
real-analysis lemma for step 6 (compare the sibling's `Zeta2Lean/Proofs/Asymptotics.lean`, which
does the `Φ_n` asymptotics for `{7,9,11}`).

**Lean hints.** `padicValRat.mul`, `padicValRat.min_le_padicValRat_add`, `padicValRat.pow`,
`padicValNat.factorial` / `sub_one_mul_padicValNat_factorial` (Legendre),
`Nat.factorization_lcmUpto`, `Nat.factorization_prod`, `Rat.den_eq_one_iff`,
`Nat.eq_one_iff_not_exists_prime_dvd`, `Chebyshev.theta`, `Chebyshev.psi`,
`Chebyshev.theta_le_log4_mul_x`, `Chebyshev.psi_eq_log_lcmUpto`, `Padic.norm_p_pow`,
`Padic.norm_natCast_eq_one_iff`; for the `ε`-power-series step, work with `PowerSeries.coeff` and
the `q`-adic valuation of coefficients of products (`PowerSeries.coeff_mul`).

**Numerical check.** `python/pair_mirror.py`, section "GAP data for configuration E" (column
`lnDodd/n`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Pair

theorem Denominators_proof (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (hCI : Stmt_CrudeInt) :
    Stmt_Denominators configE deltaE := by
  sorry

end Zeta2.Pair

end
