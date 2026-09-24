import Zeta2Lean.Pair.Statements

/-!
# Product form of the integrand: `integrand n h x = -6 [ε³] R_n(x + 1/2 + ε)`

gap: '' (routine).

**Task.** Prove `Stmt_IntegrandTaylor` from `Stmt_PF`: for admissible `(n, h)` and `x : ℕ`,
  `integrand n h x = -6 * coeff 3 (Rser n h (x + 1/2))`,
i.e. the partial-fraction integrand is `-R_n'''(x + 1/2)`.  This is the bridge used by the 2-adic
estimates (`Stmt_Valuation`, and any Δ-calculus approach to `Stmt_Nonvanishing`), which need the
product form of `R_n`.

**Informal proof.** Put `y = x + 1/2`; `y + j > 0`, so `Stmt_PF.series` applies:
`Rser n h y = ∑_{i,k} C r_{i,k} ((C (y+k) + X)^i)⁻¹`.  For `c ≠ 0` and `i ≥ 1`,
  `coeff j ((C c + X)^i)⁻¹ = (-1)^j C(i+j-1, j) c^{-(i+j)}`,
so `coeff 3 ((C c + X)^i)⁻¹ = -(i (i+1) (i+2) / 6) c^{-(i+3)}`, and
`-6 · coeff 3 (Rser n h y) = ∑_{i,k} i(i+1)(i+2) r_{i,k} (y + k)^{-(i+3)} = integrand n h x`
(`y + k = ((x + k : ℕ) : ℚ) + 1/2`).

**Lean proof.** The closed form of the inverse power is obtained from Mathlib's
`PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one` (`∑ C(d+n, d) Xⁿ · (1 - X)^{d+1} = 1`) by
`PowerSeries.rescale (-c⁻¹)` and scaling by `c^{d+1}`: `C c + X = C c · rescale (-c⁻¹) (1 - X)`
(`inv_C_add_X_pow_succ`).  Reading off coefficient `3` gives `coeff_three_inv_C_add_X_pow`.

**Numerical check.** `python/pair_mirror.py`, section "Stmt_IntegrandTaylor".
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Pair

/-- Closed form of the inverse power: for `c ≠ 0`,
`((c + X)^{d+1})⁻¹ = c^{-(d+1)} · ∑_n C(d+n, d) (-X/c)^n`. -/
private theorem inv_C_add_X_pow_succ (c : ℚ) (hc : c ≠ 0) (d : ℕ) :
    ((C c + X : PowerSeries ℚ) ^ (d + 1))⁻¹ =
      C (c⁻¹ ^ (d + 1)) * rescale (-c⁻¹) (mk fun n => ((d + n).choose d : ℚ)) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one]
  · have h1 : (C c + X : PowerSeries ℚ) = C c * rescale (-c⁻¹) (1 - X) := by
      rw [map_sub, map_one, rescale_X, mul_sub, mul_one, ← mul_assoc, ← map_mul, mul_neg,
        mul_inv_cancel₀ hc, map_neg, map_one, neg_one_mul, sub_neg_eq_add]
    rw [h1, mul_pow, ← map_pow C, ← map_pow (rescale (-c⁻¹))]
    calc C (c⁻¹ ^ (d + 1)) * rescale (-c⁻¹) (mk fun n => ((d + n).choose d : ℚ)) *
          (C (c ^ (d + 1)) * rescale (-c⁻¹) ((1 - X) ^ (d + 1)))
        = C (c⁻¹ ^ (d + 1) * c ^ (d + 1)) *
            rescale (-c⁻¹) ((mk fun n => ((d + n).choose d : ℚ)) * (1 - X) ^ (d + 1)) := by
          rw [map_mul, map_mul]
          ring
      _ = 1 := by
          rw [mk_add_choose_mul_one_sub_pow_eq_one, ← mul_pow, inv_mul_cancel₀ hc, one_pow,
            map_one, map_one, one_mul]
  · simp [hc]

/-- `[X³] ((c + X)^i)⁻¹ = -(i (i+1) (i+2) / 6) c^{-(i+3)}` for `c ≠ 0`, `i ≥ 1`. -/
private theorem coeff_three_inv_C_add_X_pow (c : ℚ) (hc : c ≠ 0) (i : ℕ) (hi : 1 ≤ i) :
    coeff 3 ((C c + X : PowerSeries ℚ) ^ i)⁻¹ =
      -((i : ℚ) * (i + 1) * (i + 2) / 6) * c⁻¹ ^ (i + 3) := by
  obtain ⟨d, rfl⟩ : ∃ d, i = d + 1 := ⟨i - 1, by omega⟩
  rw [inv_C_add_X_pow_succ c hc d, coeff_C_mul, coeff_rescale, coeff_mk]
  have hch : (((d + 3).choose d : ℕ) : ℚ) = ((d : ℚ) + 1) * (d + 2) * (d + 3) / 6 := by
    rw [Nat.cast_choose ℚ (by omega : d ≤ d + 3), Nat.add_sub_cancel_left]
    simp [Nat.factorial]
    field_simp
    ring
  rw [hch]
  push_cast
  ring

theorem IntegrandTaylor_proof (hPF : Stmt_PF) : Stmt_IntegrandTaylor := by
  intro n h hadm x
  have hy : ∀ j ≤ n, ((x : ℚ) + 1 / 2) + (j : ℚ) ≠ 0 := by
    intro j _
    positivity
  rw [hPF.series n h _ hadm hy]
  simp only [map_sum, Finset.mul_sum]
  unfold integrand genIntegrand
  refine Finset.sum_congr rfl fun i hi => Finset.sum_congr rfl fun k _ => ?_
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  have hc : (x : ℚ) + 1 / 2 + (k : ℚ) ≠ 0 := by positivity
  rw [coeff_C_mul, coeff_three_inv_C_add_X_pow _ hc i hi1]
  have hxk : (((x + k : ℕ) : ℚ) + 1 / 2) = (x : ℚ) + 1 / 2 + (k : ℚ) := by
    push_cast
    ring
  rw [hxk]
  ring

end Zeta2.Pair

end
