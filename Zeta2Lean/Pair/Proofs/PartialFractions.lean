import Zeta2Lean.Pair.Statements

/-!
# Partial fractions of the shifted family (pair blueprint; proof.md §3 "useful formula")

gap: '' (routine).

**Task.** Prove `Stmt_PF` (no hypotheses), for admissible `(n, h)`:
* `poly`:   `Rnum n h = PFpoly n h`, i.e.
  `(2t+n) ∏_m ∏_{u ∈ [-h_m, n+h_m)} (t + 1/2 + u)
     = ∑_{i=1}^{6} ∑_{k=0}^{n} r_{i,k} (t+k)^{6-i} ∏_{j≠k} (t+j)^6`;
* `series`: at every non-pole `y` (`y + j ≠ 0` for `j ≤ n`),
  `Rser n h y = ∑_{i,k} C r_{i,k} · ((C (y+k) + X)^i)⁻¹` in `PowerSeries ℚ`.

**Informal proof of `poly`.** Put `Q = ∏_{k ≤ n} (X + k)^6` (degree `6n + 6`) and
`Δ = Rnum - PFpoly`.
1. *Degrees.* `card (offsets n (h m)) = n + 2 h_m` (`Int.card_Ico`, lengths `≥ 0`), and
   `∑_m (n + 2 h_m) = 6n` (`∑ h = 0`), so `natDegree Rnum = 6n + 1`; every summand of `PFpoly` has
   `natDegree ≤ (6 - i) + 6n ≤ 6n + 5`.  Hence `natDegree Δ ≤ 6n + 5 < 6n + 6`.
2. *Local divisibility.* For each `k ≤ n`, `(X + C k)^6 ∣ Δ`.  Shift by `-k` (`Polynomial.taylor`):
   `(X + C k)^6 ∣ p ↔ X^6 ∣ taylor (-k) p ↔ ∀ μ < 6, (taylor (-k) p).coeff μ = 0`.  Now
   * `taylor (-k) Rnum = (C (n - 2k) + C 2 * X) · ∏_m ∏_u (X + C(-k + 1/2 + u))`, whose power series
     is `(C (n-2k) + 2X) · numSer n h (-k) = Gser n h k · P_k`, `P_k := ∏_{j≠k} (C (j-k) + X)^6`
     (`P_k` is invertible in `ℚ⟦X⟧`: constant coefficient `∏ (j-k)^6 ≠ 0`);
   * `taylor (-k) PFpoly`: the summands with `k' ≠ k` contain the factor `(X + (k - k))^6 = X^6`;
     the summands with `k' = k` sum to `(∑_{μ ≤ 5} C (coeff μ (Gser n h k)) X^μ) · P_k`, which
     agrees with `Gser n h k · P_k` modulo `X^6` (note `r_{6-μ,k} = coeff μ (Gser n h k)` for
     `μ ≤ 5`).
   So the Taylor coefficients of `Δ` at `-k` below `6` vanish.
3. *Coprimality.* The `(X + C k)^6`, `k ≤ n`, are pairwise coprime, so `Q ∣ Δ`
   (`Finset.prod_dvd_of_coprime`), and `Δ = 0` because `natDegree Δ < natDegree Q`
   (`Polynomial.eq_zero_of_dvd_of_degree_lt`).

**Informal proof of `series`.** Apply the ring hom `p ↦ ((taylor y p : ℚ[X]) : ℚ⟦X⟧)` (substitution
`t = y + ε`) to `poly`: the left side becomes `(C (2y+n) + C 2 * X) · numSer n h y`, the right side
`∑ C r_{i,k} (C (y+k) + X)^{6-i} ∏_{j≠k} (C (y+j) + X)^6`.  Multiply by the inverse of
`(∏_j (C (y+j) + X))^6` (constant coefficient `∏ (y+j)^6 ≠ 0`); each summand simplifies to
`C r_{i,k} · ((C (y+k) + X)^i)⁻¹` since `(C(y+k)+X)^6 = (C(y+k)+X)^{6-i} (C(y+k)+X)^i` (`i ≤ 6`).

**Lean hints.** `Polynomial.taylor`, `Polynomial.taylor_coeff`, `Polynomial.taylor_X`,
`Polynomial.taylor_C`, `Polynomial.taylor_mul`, `Polynomial.X_pow_dvd_iff`,
`Polynomial.coeToPowerSeries.ringHom`, `Polynomial.coe_mul`, `Polynomial.coe_pow`,
`Polynomial.coeff_coe`, `PowerSeries.trunc`, `PowerSeries.coeff_trunc`,
`Polynomial.pairwise_coprime_X_sub_C`, `IsCoprime.pow`, `Finset.prod_dvd_of_coprime`,
`Polynomial.eq_zero_of_dvd_of_degree_lt`, `Polynomial.natDegree_prod_le`,
`Polynomial.natDegree_mul_le`, `Int.card_Ico`, `PowerSeries.mul_inv_cancel`,
`PowerSeries.inv_mul_cancel`, `PowerSeries.constantCoeff_inv`, `map_prod`, `map_pow`.
The sibling project's `Zeta2Lean/Proofs/PartialFractions.lean` (same statement for the uniform
`(8,3)` family) can be adapted once proved; only the numerator differs.

**Numerical check.** `python/pair_mirror.py`, section "Stmt_PF" (`poly` for `n ≤ 5`, `series` at
random rational `y`, random admissible `h`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Pair

theorem PF_proof : Stmt_PF := by
  sorry

end Zeta2.Pair

end
