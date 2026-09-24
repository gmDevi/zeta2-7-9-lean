import Zeta2Lean.Pair.Statements

/-!
# Crude integrality (certainly true; a sanity lemma and a fallback denominator)

gap: '' (routine).

**Task.** Prove `Stmt_CrudeInt` (no hypotheses), for admissible `(n, h)`:
* `coef`:  `2^{6n} (k!(n-k)!)^6 d_n^{6-i} r_{i,k} ∈ ℤ` for `1 ≤ i ≤ 6`, `k ≤ n`;
* `forms`: `ClearsDen (Dcrude n) n h`, `Dcrude n = 2^{6n} n!^6 d_{2n}^{10}`.
This deliberately avoids every delicate point of GAP 2 (no building blocks, no root trick, no
Legendre savings).  It is useless for the margin (`log Dcrude ≈ 6 n log n`), but it is an honest,
elementary common denominator.

**Informal proof of `coef`.** Write `μ = 6 - i` and `d = d_n`.  Call `f ∈ ℚ⟦X⟧` *`d`-integral*
if `d^j [X^j] f ∈ ℤ` for all `j`, i.e. `rescale d f` has integer coefficients.  Since `rescale d`
is a ring hom and the power series with integer coefficients form a subring (the range of
`PowerSeries.map (Int.castRingHom ℚ)`), `d`-integral series are closed under `+` and `*`.
`Gser n h k = (C(n-2k) + 2X) · numSer n h (-k) · P_k⁻¹`, `P_k = ∏_{j≠k} (C(j-k) + X)^6`, and
* `2^{6n} numSer n h (-k) = ∏_m ∏_u (C(2u - 2k + 1) + 2X)` has integer coefficients (there are
  exactly `∑_m (n + 2h_m) = 6n` factors — admissibility), hence is `d`-integral; so is `C(n-2k)+2X`;
* `P_k = (∏_{j≠k} (j-k))^6 · ∏_{j≠k} (1 + X/(j-k))^6` and `∏_{j≠k} (j-k) = (-1)^k k! (n-k)!`, so
  `(k!(n-k)!)^6 P_k⁻¹ = ∏_{j≠k} (1 + X/(j-k))^{-6}`; each `(1 + X/c)^{-1}` with `1 ≤ |c| ≤ n` is
  `d`-integral (`rescale d` of it is `(1 + (d/c) X)^{-1} = ∑ (-(d/c))^j X^j`, `c ∣ d`).
Hence `2^{6n} (k!(n-k)!)^6 Gser n h k` is `d`-integral; take the coefficient `μ = 6 - i`.

**Informal proof of `forms`.** `0 < Dcrude n` (`Dcrude_pos`).  With `C(n,k)^6 (k!(n-k)!)^6 = n!^6`
and `d_n ∣ d_{2n}` (`Nat.lcmUpto` is monotone in divisibility):
* `Dcrude n · c_i = ∑_k [2^{6n}(k!(n-k)!)^6 d_n^{6-i} r_{i,k}] · C(n,k)^6 · d_{2n}^{10} / d_n^{6-i}`
  is an integer,
  so `Dcrude n · Z₇ = 46080 · Dcrude n · c₃ ∈ ℤ` and likewise `Z₉`;
* `A_k^{(s)} = ∑_{ℓ<k} (2/(2ℓ+1))^s` and `2ℓ + 1 ≤ 2n - 1` divides `d_{2n}`, so
  `d_{2n}^s A_k^{(s)} ∈ ℤ`; with `d_{2n}^{10} = d_{2n}^{i+4} · d_{2n}^{6-i}` each term of
  `Dcrude n · ρ₀ = -∑ (i)₄ Dcrude n r_{i,k} A_k^{(i+4)}` is an integer.

**Lean hints.** `PowerSeries.rescale`, `PowerSeries.coeff_rescale`, `PowerSeries.map`,
`RingHom.range`, `Subring.mul_mem`, `Subring.sum_mem`, `Subring.prod_mem`,
`PowerSeries.coeff_map`, `PowerSeries.inv_eq_iff_mul_eq_one`, `PowerSeries.invOfUnit`,
`Nat.lcmUpto`, `Nat.dvd_lcmUpto` (or `Finset.dvd_lcm`), `Nat.lcmUpto_dvd_lcmUpto`/monotonicity,
`Nat.choose_mul_factorial_mul_factorial`, `Int.cast_mul`, `Int.cast_sum`, `Rat.den_eq_one_iff`.
A convenient formulation: `∃ z : ℤ, q = z` is `q ∈ Set.range (Int.cast)`, closed under `+`, `*`
(`Int.cast_add`, `Int.cast_mul`).

**Numerical check.** `python/pair_mirror.py`, section "Stmt_CrudeInt" (all small admissible cases
and configuration E at `n = 40`, `80`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Pair

theorem CrudeInt_proof : Stmt_CrudeInt := by
  sorry

end Zeta2.Pair

end
