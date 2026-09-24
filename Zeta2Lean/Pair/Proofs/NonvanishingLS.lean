import Zeta2Lean.Pair.Statements

/-!
# The Lai–Sprang condition implies nonvanishing (reduction of GAP 3 to arithmetic)

gap: '' (routine).

**Task.** Prove
`Nonvanishing_of_LaiSprang : Stmt_L1 → Stmt_LaiSprangCond cfg → Stmt_Nonvanishing cfg`
for every configuration `cfg`.  (Lai–Sprang, arXiv:2306.10393, Lemma 2.2.)

**Informal proof.** Let `ζ₂(7) = r₇`, `ζ₂(9) = r₉` with `r₇, r₉ ∈ ℚ`; put `b = r₇.den · r₉.den ≥ 1`,
`a₇ = b r₇ ∈ ℤ`, `a₉ = b r₉ ∈ ℤ`.  Apply the condition with `B = b`: frequently there is a prime
`q > b` with `ρ₀ ≠ 0`, `(Z₇ = 0 ∨ v_q ρ₀ < v_q Z₇)`, `(Z₉ = 0 ∨ v_q ρ₀ < v_q Z₉)`.  Fix such an `m`
and a limit `I` of the Riemann sums; by `Stmt_L1` (+ `linear_form_zeta`, `HasVolkenborn.unique`)
`I = Lform = ρ₀ + Z₇ r₇ + Z₉ r₉` (cast from `ℚ`).  If `I = 0` then the rational
`ρ₀ + Z₇ r₇ + Z₉ r₉` is `0` (`Rat.cast_injective`), so `b ρ₀ = -(a₇ Z₇ + a₉ Z₉)` with both sides
non-zero.  `v_q(b ρ₀) = v_q(ρ₀)` since `q ∤ b` (`q > b`).  On the other side, every non-zero
summand `a Z` has `v_q(a Z) = v_q(a) + v_q(Z) ≥ v_q(Z) > v_q(ρ₀)` (`a ∈ ℤ ∖ {0}`; `Z ≠ 0`), and
`v_q` of a non-zero sum is at least the minimum (`padicValRat.min_le_padicValRat_add`); if one
summand vanishes the other equals the sum.  Either way `v_q(ρ₀) > v_q(ρ₀)`, contradiction.

**Lean hints.** `Rat.num_div_den`, `Rat.mul_den_eq_num`, `Rat.den_pos`, `padicValRat.mul`,
`padicValRat.neg`, `padicValRat.of_int`, `padicValRat.of_nat`, `padicValInt.eq_zero_of_not_dvd`,
`padicValNat.eq_zero_of_not_dvd`, `Nat.le_of_dvd`, `padicValRat.min_le_padicValRat_add`,
`Rat.cast_injective`, `Rat.cast_add`, `Rat.cast_mul`, `HasVolkenborn.unique`,
`linear_form_zeta` (`Pair/Assembly.lean` is *not* imported here; reprove the one-line identity or
use `Stmt_L1` directly: the limit value `ρ₀ + 60 c₃ J₆ + 210 c₅ J₈` equals
`ρ₀ + Z₇ ζ₂(7) + Z₉ ζ₂(9)` by `simp [Z7, Z9, zeta2]; push_cast; norm_num; ring`).
`Fact (Nat.Prime q)` instances: `haveI := Fact.mk hq`.

**Numerical check.** `python/pair_mirror.py`, section "Stmt_LaiSprangCond".
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Pair

theorem Nonvanishing_of_LaiSprang (cfg : Config) (hL1 : Stmt_L1) (hLS : Stmt_LaiSprangCond cfg) :
    Stmt_Nonvanishing cfg := by
  sorry

end Zeta2.Pair

end
