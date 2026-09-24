import Zeta2Lean.Pair.Statements

/-!
# Parity lemma and vanishing sums for the shifted family

gap: '' (routine).

**Task.** Prove `Stmt_CoeffVanish` (fields `symm`, `c1`, `ceven`) from `Stmt_PF`, for admissible
`(n, h)`.

**Informal proof.**
* `symm` (`r_{i,n-k} = (-1)^{i+1} r_{i,k}` for `k ≤ n`): from the definitions only.  Let
  `ρ := PowerSeries.rescale (-1)` (`ε ↦ -ε`, a ring hom).  Claim `Gser n h (n-k) = -ρ (Gser n h k)`:
  - linear factor: `C (n - 2(n-k)) + 2X = -ρ (C (n - 2k) + 2X)`;
  - numerator: reindex each block by the involution `u ↦ n - 1 - u` of `[-h_m, n+h_m)`
    (`Finset.prod_nbij'`): `k - n + 1/2 + u = -((n-1-u) - k + 1/2)`, so every factor of
    `numSer n h (-(n-k))` is `-ρ` of the corresponding factor of `numSer n h (-k)`; the number of
    factors is `∑_m (n + 2 h_m) = 6n`, even, so the signs cancel;
  - denominator: reindex `j ↦ n - j` on `(range (n+1)).erase (n-k) ↔ (range (n+1)).erase k`;
    `(n - j) - (n - k) = -(j - k)`, and the sixth powers kill the signs; `ρ` commutes with `⁻¹`
    (`ρ P · ρ P⁻¹ = ρ 1 = 1`).
  Then `coeff μ (ρ f) = (-1)^μ coeff μ f` (`PowerSeries.coeff_rescale`), and with `μ = 6 - i`:
  `r_{i,n-k} = -(-1)^{6-i} r_{i,k} = (-1)^{i+1} r_{i,k}`.  For `i = 0` or `i > 6` both sides are
  `0`.
* `c1` (`∑_k r_{1,k} = 0`, "`deg R_n = -5 ≤ -2`"): compare the coefficients of `t^{6n+5}` in
  `Stmt_PF.poly`.  `natDegree Rnum = 6n + 1 < 6n + 5` (admissible: `6n` numerator factors), so the
  left coefficient is `0`.  In `PFpoly`, the terms with `i ≥ 2` have `natDegree ≤ 6n + 4`, and for
  `i = 1` the polynomial `(t+k)^5 ∏_{j≠k} (t+j)^6` is monic of `natDegree 6n + 5`; so the right
  coefficient is `∑_k r_{1,k} = csum n h 1`.
* `ceven`: for even `i`, `symm` gives `r_{i,n-k} = -r_{i,k}`; reflecting the sum
  (`Finset.sum_range_reflect`) gives `c_i = -c_i`, so `c_i = 0`.

**Lean hints.** `PowerSeries.rescale`, `PowerSeries.coeff_rescale`, `PowerSeries.rescale_X`,
`PowerSeries.rescale_C` (or `map_...` lemmas), `map_prod`, `map_pow`, `map_mul`,
`PowerSeries.inv_eq_iff_mul_eq_one`, `PowerSeries.constantCoeff_inv`, `Finset.prod_nbij'`,
`Finset.prod_bij`, `Int.card_Ico`, `Finset.sum_range_reflect`,
`Polynomial.coeff_eq_zero_of_natDegree_lt`, `Polynomial.Monic.coeff_natDegree`,
`Polynomial.monic_prod_of_monic`, `Polynomial.monic_X_add_C`, `Polynomial.natDegree_prod_of_monic`,
`Polynomial.finset_sum_coeff`, `Polynomial.coeff_C_mul`, `Even.neg_one_pow`, `Odd.neg_one_pow`.
The sibling's `Zeta2Lean/Proofs/CoeffVanish.lean` has the same structure for `a = 8`.

**Numerical check.** `python/pair_mirror.py`, section "Stmt_CoeffVanish".
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Pair

theorem CoeffVanish_proof (hPF : Stmt_PF) : Stmt_CoeffVanish := by
  sorry

end Zeta2.Pair

end
