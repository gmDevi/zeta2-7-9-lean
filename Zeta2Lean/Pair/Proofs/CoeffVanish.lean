import Zeta2Lean.Pair.Statements

/-!
# Parity lemma and vanishing sums for the shifted family

gap: '' (routine).

**Status: proved** (complete, kernel-checked; `#print axioms CoeffVanish_proof` gives
`[propext, Classical.choice, Quot.sound]`).  Admissibility is used only through
`n + 2h_m ≥ 0` and `∑ h_m = 0` (number of numerator factors `= 6n`, even; `cvp_card_sum`).

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
`Zeta2Lean/Proofs/CoeffVanish.lean` of the `{7,9,11}` repository has the same structure for
`a = 8`.

**Numerical check.** `python/pair_mirror.py`, section "Stmt_CoeffVanish".
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Pair

/-! ### `symm`: the reflection `ε ↦ -ε` -/

/-- `rescale a` fixes constants. -/
private lemma cvp_rescale_C (a r : ℚ) : rescale a (C r) = C r := by
  ext m
  rw [coeff_rescale, coeff_C]
  split_ifs with hm
  · subst hm
    simp
  · simp

/-- `rescale a` commutes with the power-series inverse (over a field; both sides are `0` when the
constant coefficient vanishes). -/
private lemma cvp_rescale_inv (a : ℚ) (φ : PowerSeries ℚ) :
    rescale a φ⁻¹ = (rescale a φ)⁻¹ := by
  have hc : constantCoeff (rescale a φ) = constantCoeff φ := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_rescale, pow_zero, one_mul,
      coeff_zero_eq_constantCoeff_apply]
  by_cases hφ : constantCoeff φ = 0
  · rw [PowerSeries.inv_eq_zero.mpr hφ, map_zero, PowerSeries.inv_eq_zero.mpr (hc.trans hφ)]
  · rw [PowerSeries.eq_inv_iff_mul_eq_one (hc ▸ hφ), ← map_mul, PowerSeries.inv_mul_cancel φ hφ,
      map_one]

/-- For admissible `(n, h)` the six numerator blocks have `∑_m (n + 2 h_m) = 6n` factors. -/
private lemma cvp_card_sum (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) :
    ∑ m : Fin 6, (offsets n (h m)).card = 6 * n := by
  have key : ∀ m, ((offsets n (h m)).card : ℤ) = n + 2 * h m := by
    intro m
    have := hh.len_nonneg m
    rw [offsets, Int.card_Ico, Int.toNat_of_nonneg (by omega)]
    ring
  have hsum : ((∑ m : Fin 6, (offsets n (h m)).card : ℕ) : ℤ) = 6 * n := by
    push_cast
    simp only [key, Finset.sum_add_distrib, ← Finset.mul_sum, hh.sum_eq]
    simp
  exact_mod_cast hsum

/-- One numerator block under the reflection `u ↦ n - 1 - u` of `[-h, n+h)`:
`∏_u (k - n + 1/2 + u + ε) = (-1)^{#} ∏_u (-k + 1/2 + u - ε)`. -/
private lemma cvp_block (n k : ℕ) (hk : k ≤ n) (hm : ℤ) :
    ∏ u ∈ offsets n hm, (C (-((n - k : ℕ) : ℚ) + 1 / 2 + (u : ℚ)) + X) =
      (-1) ^ (offsets n hm).card *
        rescale (-1 : ℚ) (∏ u ∈ offsets n hm, (C (-(k : ℚ) + 1 / 2 + (u : ℚ)) + X)) := by
  rw [map_prod, ← Finset.prod_neg]
  refine Finset.prod_nbij' (fun u => (n : ℤ) - 1 - u) (fun u => (n : ℤ) - 1 - u) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [offsets, Finset.mem_Ico] at hu ⊢
    omega
  · intro u hu
    simp only [offsets, Finset.mem_Ico] at hu ⊢
    omega
  · intro u _
    ring
  · intro u _
    ring
  · intro u _
    rw [map_add (rescale (-1 : ℚ)), cvp_rescale_C, rescale_neg_one_X, Nat.cast_sub hk]
    have e : (-((n : ℚ) - k) + 1 / 2 + (u : ℚ)) =
        -(-(k : ℚ) + 1 / 2 + (((n : ℤ) - 1 - u : ℤ) : ℚ)) := by
      push_cast
      ring
    rw [e, map_neg]
    ring

/-- `numSer n h (-(n-k)) = numSer n h (-k)` evaluated at `-ε` (the signs cancel: `6n` factors). -/
private lemma cvp_numSer (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) (k : ℕ) (hk : k ≤ n) :
    numSer n h (-((n - k : ℕ) : ℚ)) = rescale (-1 : ℚ) (numSer n h (-(k : ℚ))) := by
  unfold numSer
  rw [map_prod, Finset.prod_congr rfl (fun m _ => cvp_block n k hk (h m)),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, cvp_card_sum n h hh,
    (show Even (6 * n) from ⟨3 * n, by ring⟩).neg_one_pow, one_mul]

/-- The denominator under `j ↦ n - j`. -/
private lemma cvp_den (n k : ℕ) (hk : k ≤ n) :
    ∏ j ∈ (range (n + 1)).erase (n - k), (C ((j : ℚ) - ((n - k : ℕ) : ℚ)) + X) ^ 6 =
      rescale (-1 : ℚ) (∏ j ∈ (range (n + 1)).erase k, (C ((j : ℚ) - k) + X) ^ 6) := by
  rw [map_prod]
  refine Finset.prod_nbij' (fun j => n - j) (fun j => n - j) ?_ ?_ ?_ ?_ ?_
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj ⊢
    omega
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    omega
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    omega
  · intro j hj
    simp only [Finset.mem_erase, Finset.mem_range] at hj
    simp only [map_pow, map_add, cvp_rescale_C, rescale_neg_one_X]
    rw [Nat.cast_sub hk, Nat.cast_sub (by omega : j ≤ n)]
    have e : ((j : ℚ) - ((n : ℚ) - k)) = -((n : ℚ) - j - k) := by ring
    rw [e, map_neg]
    ring

/-- `G_{n-k}(ε) = -G_k(-ε)`. -/
private lemma cvp_Gser_reflect (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) (k : ℕ)
    (hk : k ≤ n) : Gser n h (n - k) = -rescale (-1 : ℚ) (Gser n h k) := by
  unfold Gser
  rw [cvp_numSer n h hh k hk, cvp_den n k hk]
  simp only [map_mul, map_add, cvp_rescale_C, rescale_neg_one_X, cvp_rescale_inv]
  have h1 : (C ((n : ℚ) - 2 * ((n - k : ℕ) : ℚ)) : PowerSeries ℚ) = -C ((n : ℚ) - 2 * k) := by
    rw [← map_neg]
    congr 1
    rw [Nat.cast_sub hk]
    ring
  rw [h1]
  ring

/-- `[ε^μ] G_{n-k} = -(-1)^μ [ε^μ] G_k`. -/
private lemma cvp_coeff_Gser_reflect (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) (k μ : ℕ)
    (hk : k ≤ n) : coeff μ (Gser n h (n - k)) = -((-1 : ℚ) ^ μ * coeff μ (Gser n h k)) := by
  rw [cvp_Gser_reflect n h hh k hk, map_neg, coeff_rescale]

/-- `r_{i,n-k} = (-1)^{i+1} r_{i,k}`. -/
private lemma cvp_symm (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) (i k : ℕ) (hk : k ≤ n) :
    rcoef n h i (n - k) = (-1) ^ (i + 1) * rcoef n h i k := by
  unfold rcoef
  by_cases hi : 1 ≤ i ∧ i ≤ 6
  · rw [ite_eq_left ⟨hi.1, hi.2, Nat.sub_le n k⟩, ite_eq_left ⟨hi.1, hi.2, hk⟩,
      cvp_coeff_Gser_reflect n h hh k _ hk]
    obtain ⟨h1, h6⟩ := hi
    interval_cases i <;> norm_num
  · rw [ite_eq_right (fun hc => hi ⟨hc.1, hc.2.1⟩), ite_eq_right (fun hc => hi ⟨hc.1, hc.2.1⟩),
      mul_zero]

/-! ### `c1`: the top coefficient of `Stmt_PF.poly` -/

private lemma cvp_monic_block (n : ℕ) (hm : ℤ) :
    (∏ u ∈ offsets n hm, (Polynomial.X + Polynomial.C (1 / 2 + (u : ℚ)))).Monic :=
  Polynomial.monic_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)

private lemma cvp_natDegree_block (n : ℕ) (hm : ℤ) :
    (∏ u ∈ offsets n hm, (Polynomial.X + Polynomial.C (1 / 2 + (u : ℚ)))).natDegree =
      (offsets n hm).card := by
  rw [Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => Polynomial.monic_X_add_C _)]
  simp only [Polynomial.natDegree_X_add_C, Finset.sum_const, smul_eq_mul, mul_one]

/-- `natDegree Rnum ≤ 6n + 1`. -/
private lemma cvp_natDegree_Rnum (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) :
    (Rnum n h).natDegree ≤ 6 * n + 1 := by
  unfold Rnum
  have hprod : (∏ m : Fin 6, ∏ u ∈ offsets n (h m),
      (Polynomial.X + Polynomial.C (1 / 2 + (u : ℚ)))).natDegree = 6 * n := by
    rw [Polynomial.natDegree_prod_of_monic _ _ (fun m _ => cvp_monic_block n (h m))]
    simp only [cvp_natDegree_block]
    exact cvp_card_sum n h hh
  have hA : (Polynomial.C (2 : ℚ) * Polynomial.X + Polynomial.C (n : ℚ)).natDegree ≤ 1 :=
    Polynomial.natDegree_linear_le
  refine Polynomial.natDegree_mul_le.trans ?_
  omega

/-- The `(i,k)` basis polynomial `(t+k)^{6-i} ∏_{j ≠ k} (t+j)^6` is monic ... -/
private lemma cvp_monic_term (n i k : ℕ) :
    ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (6 - i) *
      ∏ j ∈ (range (n + 1)).erase k, (Polynomial.X + Polynomial.C (j : ℚ)) ^ 6).Monic :=
  ((Polynomial.monic_X_add_C _).pow _).mul
    (Polynomial.monic_prod_of_monic _ _ (fun _ _ => (Polynomial.monic_X_add_C _).pow 6))

/-- ... of degree `(6 - i) + 6n` (for `k ≤ n`). -/
private lemma cvp_natDegree_term (n i k : ℕ) (hk : k ∈ range (n + 1)) :
    ((Polynomial.X + Polynomial.C (k : ℚ)) ^ (6 - i) *
      ∏ j ∈ (range (n + 1)).erase k, (Polynomial.X + Polynomial.C (j : ℚ)) ^ 6).natDegree =
      (6 - i) + 6 * n := by
  rw [Polynomial.Monic.natDegree_mul ((Polynomial.monic_X_add_C _).pow _)
      (Polynomial.monic_prod_of_monic _ _ (fun _ _ => (Polynomial.monic_X_add_C _).pow 6)),
    Polynomial.natDegree_prod_of_monic _ _ (fun _ _ => (Polynomial.monic_X_add_C _).pow 6)]
  simp only [Polynomial.natDegree_pow, Polynomial.natDegree_X_add_C, mul_one, Finset.sum_const,
    smul_eq_mul, Finset.card_erase_of_mem hk, Finset.card_range, Nat.add_sub_cancel]
  ring

/-- The coefficient of `t^{6n+5}` in `PFpoly n h` is `c₁`. -/
private lemma cvp_coeff_PFpoly (n : ℕ) (h : Fin 6 → ℤ) :
    (PFpoly n h).coeff (6 * n + 5) = csum n h 1 := by
  unfold PFpoly csum genCsum
  rw [Polynomial.finsetSum_coeff, Finset.sum_eq_single 1]
  · rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_congr rfl (fun k hk => ?_)
    rw [mul_assoc, Polynomial.coeff_C_mul]
    have hdeg := cvp_natDegree_term n 1 k hk
    rw [show 6 - 1 + 6 * n = 6 * n + 5 by omega] at hdeg
    rw [← hdeg, (cvp_monic_term n 1 k).coeff_natDegree, mul_one]
  · intro i hi hi1
    rw [Polynomial.finsetSum_coeff]
    refine Finset.sum_eq_zero (fun k hk => ?_)
    rw [mul_assoc, Polynomial.coeff_C_mul, Polynomial.coeff_eq_zero_of_natDegree_lt, mul_zero]
    rw [cvp_natDegree_term n i k hk]
    have := (Finset.mem_Icc.mp hi).1
    omega
  · intro hc
    exact absurd (Finset.mem_Icc.mpr ⟨le_refl 1, by norm_num⟩) hc

/-- `c₁ = 0`. -/
private lemma cvp_c1 (hPF : Stmt_PF) (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) :
    csum n h 1 = 0 := by
  rw [← cvp_coeff_PFpoly n h, ← hPF.poly n h hh]
  exact Polynomial.coeff_eq_zero_of_natDegree_lt ((cvp_natDegree_Rnum n h hh).trans_lt (by omega))

/-! ### `ceven` -/

/-- `c_i = 0` for even `i`. -/
private lemma cvp_ceven (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) (i : ℕ) (hi : Even i) :
    csum n h i = 0 := by
  have h1 := Finset.sum_range_reflect (fun k => rcoef n h i k) (n + 1)
  have h2 : ∑ j ∈ range (n + 1), rcoef n h i (n + 1 - 1 - j) = -csum n h i := by
    unfold csum genCsum
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl (fun j hj => ?_)
    have hj' : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    rw [Nat.add_sub_cancel, cvp_symm n h hh i j hj', hi.add_one.neg_one_pow, neg_one_mul]
  have h3 : ∑ j ∈ range (n + 1), rcoef n h i j = csum n h i := rfl
  rw [h2, h3] at h1
  linarith

theorem CoeffVanish_proof (hPF : Stmt_PF) : Stmt_CoeffVanish where
  symm := cvp_symm
  c1 := cvp_c1 hPF
  ceven := cvp_ceven

end Zeta2.Pair

end
