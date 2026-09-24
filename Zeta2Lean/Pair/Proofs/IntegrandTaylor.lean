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

**Lean hints.** `PowerSeries.coeff_mul`, `map_sum`, `PowerSeries.coeff_C_mul`; for the inverse
power, either prove the closed form by `PowerSeries.eq_inv_iff_mul_eq_one` (the candidate
`mk fun j => (-1)^j * choose (i+j-1) j * c⁻¹^(i+j)` times `(C c + X)^i` is `1`: induct on `i`
using `(C c + X) * mk (fun j => (-1)^j c^{-(j+1)}) = 1`), or compute the first four coefficients
directly from `((C c + X)^i) * ((C c + X)^i)⁻¹ = 1` (`PowerSeries.mul_inv_cancel`,
`PowerSeries.coeff_mul`, `Finset.antidiagonal`).  `Nat.cast_add`, `push_cast`, `field_simp`, `ring`.

**Numerical check.** `python/pair_mirror.py`, section "Stmt_IntegrandTaylor".
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Pair

theorem IntegrandTaylor_proof (hPF : Stmt_PF) : Stmt_IntegrandTaylor := by
  sorry

end Zeta2.Pair

end
