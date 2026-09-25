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

**Numerical check.** `python/pair_mirror.py`, section "Stmt_CrudeInt" (all small admissible cases
and configuration E at `n = 40`, `80`).

**Formalisation (complete, no proof holes; axioms: propext, Classical.choice, Quot.sound).**
Modelled on `Zeta2Lean/Proofs/DenomL2a.lean` of the `{7,9,11}` repository.
* `crudeDInt d := crudeIntPS.comap (rescale d)` is the subring of `d`-integral series
  (`crude_mem_DInt_iff`: `∀ j, ∃ z : ℤ, d^j * coeff j A = z`).
* `crude_geom_mem`: `C c · (C c + X)⁻¹ ∈ crudeDInt N` for an integer `c ≠ 0` with `c ∣ N`
  (`c` may be negative: the poles `j < k` give `c = j - k < 0`).
* `crude_num_mem`: `C (2^{6n}) · numSer n h (-k)` is a product of `C(2u-2k+1) + C 2 · X`
  (`crude_sum_card`: `∑_m #(offsets n (h m)) = 6n`, from `∑ h = 0` and `n + 2h_m ≥ 0`; the
  critical-zero part of `Admissible` is not used).
* `crude_den_mem`: `C((k!(n-k)!)^6) · (∏_{j≠k} (C(j-k)+X)^6)⁻¹ = ∏_{j≠k} (C(j-k)·(C(j-k)+X)⁻¹)^6`
  via `crude_prod_sub` (`∏_{j≠k} (j-k) = (-1)^k k!(n-k)!`) and `crude_prod_inv`.
* `forms` works in the subring `⊥ : Subring ℚ` (= `ℤ`, `crude_mem_bot_iff`):
  `crude_Ahalf_mem` (`d_{2n}^s A_k^{(s)} ∈ ℤ`), `crude_rcoef_mem`
  (`2^{6n} n!^6 d_{2n}^{6-i} r_{i,k} ∈ ℤ`, from `coef`, `n! = k!(n-k)! C(n,k)` and
  `d_{2n} = d_n e`), `crude_Dr_mem` (`Dcrude n · r_{i,k} · x ∈ ℤ` if `d_{2n}^{i+4} x ∈ ℤ`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Pair

/-! ### `d`-integral power series -/

/-- Power series over `ℚ` with integer coefficients (the image of `ℤ⟦X⟧`), a subring. -/
private def crudeIntPS : Subring (PowerSeries ℚ) :=
  (PowerSeries.map (Int.castRingHom ℚ)).range

private lemma crude_mem_intPS_iff (B : PowerSeries ℚ) :
    B ∈ crudeIntPS ↔ ∀ j, ∃ z : ℤ, coeff j B = z := by
  constructor
  · rintro ⟨B', rfl⟩ j
    exact ⟨coeff j B', by simp [coeff_map]⟩
  · intro h
    choose z hz using h
    refine ⟨PowerSeries.mk z, ?_⟩
    ext j
    rw [coeff_map, coeff_mk, hz j, eq_intCast]

/-- `d`-integral power series (`d^j · [X^j] A ∈ ℤ` for all `j`): the preimage of `crudeIntPS`
under the ring homomorphism `rescale d`, hence a subring. -/
private def crudeDInt (d : ℚ) : Subring (PowerSeries ℚ) :=
  crudeIntPS.comap (rescale d)

private lemma crude_mem_DInt_iff (d : ℚ) (A : PowerSeries ℚ) :
    A ∈ crudeDInt d ↔ ∀ j, ∃ z : ℤ, d ^ j * coeff j A = z := by
  simp only [crudeDInt, Subring.mem_comap, crude_mem_intPS_iff, coeff_rescale]

private lemma crude_C_int_mem (d : ℚ) (z : ℤ) : C (z : ℚ) ∈ crudeDInt d := by
  rw [map_intCast]
  exact intCast_mem _ z

private lemma crude_X_mem (N : ℕ) : (X : PowerSeries ℚ) ∈ crudeDInt (N : ℚ) := by
  rw [crude_mem_DInt_iff]
  intro j
  by_cases hj : j = 1
  · subst hj
    exact ⟨N, by simp⟩
  · exact ⟨0, by simp [coeff_X, hj]⟩

/-- The geometric series `c · (c + X)⁻¹ = ∑_j (-1/c)^j X^j` is `N`-integral when `c ∣ N`
(`c` a non-zero integer, possibly negative). -/
private lemma crude_geom_mem (N : ℕ) (c : ℤ) (hc : c ≠ 0) (hcN : c ∣ (N : ℤ)) :
    C (c : ℚ) * (C (c : ℚ) + X)⁻¹ ∈ crudeDInt (N : ℚ) := by
  have hcq : (c : ℚ) ≠ 0 := Int.cast_ne_zero.mpr hc
  set G : PowerSeries ℚ := PowerSeries.mk fun j => (-1 / (c : ℚ)) ^ j with hG
  have hGmul : G * (C (c : ℚ) + X) = C (c : ℚ) := by
    have h1 : G * (C (c : ℚ) + X) = C (c : ℚ) * G + G * X := by ring
    rw [h1]
    ext j
    rcases j with _ | j
    · simp [hG]
    · rw [map_add, coeff_C_mul, coeff_succ_mul_X, coeff_C]
      simp only [hG, coeff_mk, Nat.succ_ne_zero, ite_false]
      have hce : (c : ℚ) * (-1 / c) = -1 := by field_simp
      calc (c : ℚ) * (-1 / (c : ℚ)) ^ (j + 1) + (-1 / (c : ℚ)) ^ j
          = (-1 / (c : ℚ)) ^ j * ((c : ℚ) * (-1 / c) + 1) := by ring
        _ = 0 := by rw [hce]; ring
  have hconst : constantCoeff (C (c : ℚ) + X) ≠ 0 := by simp [hcq]
  have hinv : (C (c : ℚ) + X)⁻¹ = C ((c : ℚ)⁻¹) * G := by
    rw [PowerSeries.inv_eq_iff_mul_eq_one hconst, mul_assoc, hGmul, ← map_mul,
      inv_mul_cancel₀ hcq, map_one]
  rw [hinv, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hcq, map_one, one_mul, crude_mem_DInt_iff]
  intro j
  obtain ⟨q, hq⟩ := hcN
  refine ⟨(-q) ^ j, ?_⟩
  simp only [hG, coeff_mk]
  rw [← mul_pow]
  push_cast
  congr 1
  have hN : (N : ℚ) = c * q := by exact_mod_cast hq
  rw [hN]
  field_simp

/-! ### `d_n = lcm(1, …, n)` -/

private lemma crude_dvd_dn {i n : ℕ} (hi1 : 1 ≤ i) (hin : i ≤ n) : i ∣ dn n := by
  unfold dn Nat.lcmUpto
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hi1, hin⟩)

private lemma crude_dn_dvd_dn {m n : ℕ} (hmn : m ≤ n) : dn m ∣ dn n := by
  unfold dn Nat.lcmUpto
  refine Finset.lcm_dvd (fun b hb => ?_)
  have hb' := Finset.mem_Icc.mp hb
  exact Finset.dvd_lcm (f := id) (Finset.mem_Icc.mpr ⟨hb'.1, hb'.2.trans hmn⟩)

/-! ### The numerator: `2^{6n} numSer n h (-k)` has integer coefficients -/

private lemma crude_card_offsets (n : ℕ) (h : ℤ) (hh : 0 ≤ (n : ℤ) + 2 * h) :
    ((offsets n h).card : ℤ) = n + 2 * h := by
  rw [offsets, Int.card_Ico, Int.toNat_of_nonneg (by linarith)]
  ring

/-- The numerator has exactly `∑_m (n + 2 h_m) = 6n` linear factors. -/
private lemma crude_sum_card (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) :
    ∑ m : Fin 6, (offsets n (h m)).card = 6 * n := by
  have key : ((∑ m : Fin 6, (offsets n (h m)).card : ℕ) : ℤ) = ((6 * n : ℕ) : ℤ) := by
    push_cast
    rw [Finset.sum_congr rfl (fun m _ => crude_card_offsets n (h m) (hh.len_nonneg m)),
      Finset.sum_add_distrib, ← Finset.mul_sum, hh.sum_eq]
    simp
  exact_mod_cast key

private lemma crude_num_mem (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) (k d : ℕ) :
    C ((2 : ℚ) ^ (6 * n)) * numSer n h (-(k : ℚ)) ∈ crudeDInt (d : ℚ) := by
  have heq : C ((2 : ℚ) ^ (6 * n)) * numSer n h (-(k : ℚ)) =
      ∏ m : Fin 6, ∏ u ∈ offsets n (h m), (C (((2 * u - 2 * k + 1 : ℤ)) : ℚ) + C 2 * X) := by
    calc C ((2 : ℚ) ^ (6 * n)) * numSer n h (-(k : ℚ))
        = ∏ m : Fin 6, ∏ u ∈ offsets n (h m), (C 2 * (C (-(k : ℚ) + 1 / 2 + (u : ℚ)) + X)) := by
          simp only [Finset.prod_mul_distrib, Finset.prod_const]
          rw [Finset.prod_pow_eq_pow_sum, crude_sum_card n h hh, map_pow, numSer]
      _ = ∏ m : Fin 6, ∏ u ∈ offsets n (h m), (C (((2 * u - 2 * k + 1 : ℤ)) : ℚ) + C 2 * X) := by
          refine Finset.prod_congr rfl (fun m _ => Finset.prod_congr rfl (fun u _ => ?_))
          rw [mul_add, ← map_mul]
          congr 2
          push_cast
          ring
  rw [heq]
  refine Subring.prod_mem _ (fun m _ => Subring.prod_mem _ (fun u _ => ?_))
  refine Subring.add_mem _ (crude_C_int_mem _ _) (Subring.mul_mem _ ?_ (crude_X_mem _))
  have := crude_C_int_mem (d : ℚ) 2
  push_cast at this
  exact this

/-! ### The pole factor: `(k!(n-k)!)^6 (∏_{j≠k} (j-k+ε)^6)⁻¹` is `d_n`-integral -/

private lemma crude_prod_range_sub (k : ℕ) :
    ∏ j ∈ range k, ((j : ℚ) - k) = (-1) ^ k * k.factorial := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.prod_range_succ', Nat.factorial_succ]
    have hterm : ∀ j ∈ range k, (((j + 1 : ℕ) : ℚ) - ((k + 1 : ℕ) : ℚ)) = (j : ℚ) - k := by
      intro j _
      push_cast
      ring
    rw [Finset.prod_congr rfl hterm, ih]
    push_cast
    ring

/-- `∏_{j ≤ n, j ≠ k} (j - k) = (-1)^k k! (n-k)!`. -/
private lemma crude_prod_sub (n k : ℕ) (hk : k ≤ n) :
    ∏ j ∈ (range (n + 1)).erase k, ((j : ℚ) - k) =
      (-1) ^ k * ((k.factorial : ℚ) * (n - k).factorial) := by
  induction n, hk using Nat.le_induction with
  | base =>
    rw [Finset.range_add_one, Finset.erase_insert Finset.notMem_range_self, Nat.sub_self,
      Nat.factorial_zero, Nat.cast_one, mul_one]
    exact crude_prod_range_sub k
  | succ n hkn ih =>
    rw [Finset.range_add_one (n := n + 1), Finset.erase_insert_of_ne (by omega),
      Finset.prod_insert (by simp), ih, show n + 1 - k = (n - k) + 1 by omega,
      Nat.factorial_succ]
    push_cast [Nat.cast_sub hkn]
    ring

private lemma crude_prod_inv {ι : Type*} (s : Finset ι) (φ : ι → PowerSeries ℚ) :
    (∏ j ∈ s, φ j)⁻¹ = ∏ j ∈ s, (φ j)⁻¹ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, PowerSeries.mul_inv_rev, ih, mul_comm]

private lemma crude_den_mem (n k : ℕ) (hk : k ≤ n) :
    C ((((k.factorial * (n - k).factorial : ℕ) : ℚ)) ^ 6) *
      (∏ j ∈ (range (n + 1)).erase k, (C ((j : ℚ) - k) + X) ^ 6)⁻¹ ∈ crudeDInt (dn n : ℚ) := by
  have hmem : ∀ j ∈ (range (n + 1)).erase k,
      C ((j : ℚ) - k) * (C ((j : ℚ) - k) + X)⁻¹ ∈ crudeDInt (dn n : ℚ) := by
    intro j hj
    have hjk : j ≠ k := Finset.ne_of_mem_erase hj
    have hjn : j ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp (Finset.mem_of_mem_erase hj))
    have hdvd : ((j : ℤ) - k) ∣ ((dn n : ℕ) : ℤ) := by
      rw [← Int.natAbs_dvd_natAbs, Int.natAbs_natCast]
      exact crude_dvd_dn (by omega) (by omega)
    have := crude_geom_mem (dn n) ((j : ℤ) - k) (by omega) hdvd
    push_cast at this
    exact this
  have hW := Subring.prod_mem _ (fun j hj => Subring.pow_mem _ (hmem j hj) 6)
  convert hW using 1
  simp only [mul_pow, Finset.prod_mul_distrib, PowerSeries.inv_pow, ← crude_prod_inv]
  congr 1
  rw [Finset.prod_pow, ← map_prod, ← map_pow, crude_prod_sub n k hk]
  congr 1
  rw [mul_pow, ← pow_mul, Even.neg_one_pow ⟨3 * k, by ring⟩, one_mul]
  push_cast
  ring

/-! ### `coef` -/

/-- `2^{6n} (k!(n-k)!)^6 G_k(ε)` is `d_n`-integral. -/
private lemma crude_Gser_mem (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) (k : ℕ)
    (hk : k ≤ n) :
    C ((2 : ℚ) ^ (6 * n) * (((k.factorial * (n - k).factorial : ℕ) : ℚ)) ^ 6) * Gser n h k ∈
      crudeDInt (dn n : ℚ) := by
  have hlin : C ((n : ℚ) - 2 * k) + C 2 * X ∈ crudeDInt (dn n : ℚ) := by
    refine Subring.add_mem _ ?_ (Subring.mul_mem _ ?_ (crude_X_mem _))
    · have := crude_C_int_mem (dn n : ℚ) ((n : ℤ) - 2 * k)
      push_cast at this
      exact this
    · have := crude_C_int_mem (dn n : ℚ) 2
      push_cast at this
      exact this
  have heq : C ((2 : ℚ) ^ (6 * n) * (((k.factorial * (n - k).factorial : ℕ) : ℚ)) ^ 6) *
      Gser n h k =
      (C ((n : ℚ) - 2 * k) + C 2 * X) * (C ((2 : ℚ) ^ (6 * n)) * numSer n h (-(k : ℚ))) *
      (C ((((k.factorial * (n - k).factorial : ℕ) : ℚ)) ^ 6) *
        (∏ j ∈ (range (n + 1)).erase k, (C ((j : ℚ) - k) + X) ^ 6)⁻¹) := by
    rw [Gser, map_mul]
    ring
  rw [heq]
  exact Subring.mul_mem _ (Subring.mul_mem _ hlin (crude_num_mem n h hh k _))
    (crude_den_mem n k hk)

private theorem crude_coef (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) (i k : ℕ)
    (hi1 : 1 ≤ i) (hi6 : i ≤ 6) (hk : k ≤ n) :
    ∃ z : ℤ, (2 : ℚ) ^ (6 * n) * ((k.factorial * (n - k).factorial : ℕ) : ℚ) ^ 6 *
      (dn n : ℚ) ^ (6 - i) * rcoef n h i k = z := by
  obtain ⟨z, hz⟩ := (crude_mem_DInt_iff _ _).1 (crude_Gser_mem n h hh k hk) (6 - i)
  refine ⟨z, ?_⟩
  rw [coeff_C_mul] at hz
  simp only [rcoef, hi1, hi6, hk, and_self, ↓reduceIte]
  rw [← hz]
  ring

/-! ### `forms` -/

private lemma crude_mem_bot_iff (q : ℚ) : q ∈ (⊥ : Subring ℚ) ↔ ∃ z : ℤ, q = z := by
  rw [Subring.mem_bot]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩

/-- `d_{2n}^s A_k^{(s)} ∈ ℤ` for `k ≤ n`. -/
private lemma crude_Ahalf_mem (n k s : ℕ) (hk : k ≤ n) :
    (dn (2 * n) : ℚ) ^ s * Ahalf k s ∈ (⊥ : Subring ℚ) := by
  unfold Ahalf
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ (fun l hl => ?_)
  have hl : l < k := Finset.mem_range.mp hl
  obtain ⟨q, hq⟩ := crude_dvd_dn (i := 2 * l + 1) (n := 2 * n) (by omega) (by omega)
  have hq' : (dn (2 * n) : ℚ) = (2 * l + 1) * q := by exact_mod_cast hq
  rw [← mul_pow, hq']
  have hne : (l : ℚ) + 1 / 2 ≠ 0 := by positivity
  have key : (2 * (l : ℚ) + 1) * q * ((l : ℚ) + 1 / 2)⁻¹ = ((2 * q : ℕ) : ℚ) := by
    field_simp
    push_cast
    ring
  rw [key, ← Nat.cast_pow]
  exact natCast_mem _ _

/-- `2^{6n} n!^6 d_{2n}^{6-i} r_{i,k} ∈ ℤ`. -/
private lemma crude_rcoef_mem (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) (i k : ℕ)
    (hi1 : 1 ≤ i) (hi6 : i ≤ 6) (hk : k ≤ n) :
    (2 : ℚ) ^ (6 * n) * (n.factorial : ℚ) ^ 6 * (dn (2 * n) : ℚ) ^ (6 - i) * rcoef n h i k ∈
      (⊥ : Subring ℚ) := by
  obtain ⟨z, hz⟩ := crude_coef n h hh i k hi1 hi6 hk
  obtain ⟨e, he⟩ := crude_dn_dvd_dn (m := n) (n := 2 * n) (by omega)
  have he' : (dn (2 * n) : ℚ) = (dn n : ℚ) * e := by exact_mod_cast he
  have hfac : (n.factorial : ℚ) =
      ((k.factorial * (n - k).factorial : ℕ) : ℚ) * (n.choose k : ℚ) := by
    rw [← Nat.choose_mul_factorial_mul_factorial hk]
    push_cast
    ring
  rw [crude_mem_bot_iff]
  refine ⟨z * (n.choose k : ℤ) ^ 6 * (e : ℤ) ^ (6 - i), ?_⟩
  rw [he', hfac]
  push_cast at hz ⊢
  linear_combination ((n.choose k : ℚ) ^ 6 * (e : ℚ) ^ (6 - i)) * hz

/-- `Dcrude n · r_{i,k} · x ∈ ℤ` whenever `d_{2n}^{i+4} x ∈ ℤ`. -/
private lemma crude_Dr_mem (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) (i k : ℕ)
    (hi1 : 1 ≤ i) (hi6 : i ≤ 6) (hk : k ≤ n) (x : ℚ)
    (hx : (dn (2 * n) : ℚ) ^ (i + 4) * x ∈ (⊥ : Subring ℚ)) :
    (Dcrude n : ℚ) * rcoef n h i k * x ∈ (⊥ : Subring ℚ) := by
  have hpow : (dn (2 * n) : ℚ) ^ 10 =
      (dn (2 * n) : ℚ) ^ (6 - i) * (dn (2 * n) : ℚ) ^ (i + 4) := by
    rw [← pow_add]
    congr 1
    omega
  have heq : (Dcrude n : ℚ) * rcoef n h i k * x =
      ((2 : ℚ) ^ (6 * n) * (n.factorial : ℚ) ^ 6 * (dn (2 * n) : ℚ) ^ (6 - i) * rcoef n h i k) *
        ((dn (2 * n) : ℚ) ^ (i + 4) * x) := by
    unfold Dcrude
    push_cast
    rw [hpow]
    ring
  rw [heq]
  exact Subring.mul_mem _ (crude_rcoef_mem n h hh i k hi1 hi6 hk) hx

/-- `Dcrude n · c_i ∈ ℤ`. -/
private lemma crude_Z_mem (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) (i : ℕ)
    (hi1 : 1 ≤ i) (hi6 : i ≤ 6) :
    (Dcrude n : ℚ) * csum n h i ∈ (⊥ : Subring ℚ) := by
  unfold csum genCsum
  rw [Finset.mul_sum]
  refine Subring.sum_mem _ (fun k hk => ?_)
  have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
  have := crude_Dr_mem n h hh i k hi1 hi6 hk' 1 (by
    rw [mul_one, ← Nat.cast_pow]
    exact natCast_mem _ _)
  rwa [mul_one] at this

theorem CrudeInt_proof : Stmt_CrudeInt where
  coef := crude_coef
  forms := by
    intro n h hh
    refine ⟨Dcrude_pos n, ?_, ?_, ?_⟩
    · -- `ρ₀ = -∑_{i,k} (i)₄ r_{i,k} A_k^{(i+4)}`
      rw [← crude_mem_bot_iff]
      unfold rho0 genRho0
      rw [mul_neg, Finset.mul_sum]
      refine Subring.neg_mem _ (Subring.sum_mem _ (fun i hi => ?_))
      rw [Finset.mul_sum]
      refine Subring.sum_mem _ (fun k hk => ?_)
      have hi' := Finset.mem_Icc.mp hi
      have hk' : k ≤ n := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
      have hP : ((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) =
          ((i * (i + 1) * (i + 2) * (i + 3) : ℕ) : ℚ) := by
        push_cast
        ring
      have heq : (Dcrude n : ℚ) * (((i : ℚ) * (i + 1) * (i + 2) * (i + 3)) * rcoef n h i k *
          Ahalf k (i + 4)) =
          ((i * (i + 1) * (i + 2) * (i + 3) : ℕ) : ℚ) *
            ((Dcrude n : ℚ) * rcoef n h i k * Ahalf k (i + 4)) := by
        rw [hP]
        ring
      rw [heq]
      exact Subring.mul_mem _ (natCast_mem _ _)
        (crude_Dr_mem n h hh i k hi'.1 hi'.2 hk' _ (crude_Ahalf_mem n k (i + 4) hk'))
    · -- `Z₇ = 46080 c₃`
      rw [← crude_mem_bot_iff]
      unfold Z7
      rw [mul_left_comm]
      exact Subring.mul_mem _ (by exact_mod_cast natCast_mem (⊥ : Subring ℚ) 46080)
        (crude_Z_mem n h hh 3 (by norm_num) (by norm_num))
    · -- `Z₉ = 860160 c₅`
      rw [← crude_mem_bot_iff]
      unfold Z9
      rw [mul_left_comm]
      exact Subring.mul_mem _ (by exact_mod_cast natCast_mem (⊥ : Subring ℚ) 860160)
        (crude_Z_mem n h hh 5 (by norm_num) (by norm_num))

end Zeta2.Pair

end
