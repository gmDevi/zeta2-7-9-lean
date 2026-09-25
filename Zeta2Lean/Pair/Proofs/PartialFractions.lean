import Zeta2Lean.Pair.Statements

/-!
# Partial fractions of the shifted family (pair blueprint; proof.md §3 "useful formula")

gap: '' (routine).  **Status: proved.**  `#print axioms Zeta2.Pair.PF_proof` gives
`[propext, Classical.choice, Quot.sound]`.

`Stmt_PF` has two fields, for admissible `(n, h)`:
* `poly`:   `Rnum n h = PFpoly n h`, i.e.
  `(2t+n) ∏_m ∏_{u ∈ [-h_m, n+h_m)} (t + 1/2 + u)
     = ∑_{i=1}^{6} ∑_{k=0}^{n} r_{i,k} (t+k)^{6-i} ∏_{j≠k} (t+j)^6`;
* `series`: at every non-pole `y` (`y + j ≠ 0` for `j ≤ n`),
  `Rser n h y = ∑_{i,k} C r_{i,k} · ((C (y+k) + X)^i)⁻¹` in `PowerSeries ℚ`.
Everything follows from the definition `r_{6-μ,k} = [ε^μ] G_k(ε)`.  Admissibility is used only
through `∑ h = 0` and `n + 2 h_m ≥ 0` (degree count); the critical-zero condition is not needed.

**Proof of `poly`** (`PairPF.poly_eq`).  Let `Δ := Rnum n h - PFpoly n h ∈ ℚ[t]`.
1. *Degrees.* `card (offsets n (h m)) = n + 2 h_m` (`PairPF.card_offsets`: `Int.card_Ico`, lengths
   `≥ 0`) and `∑_m (n + 2 h_m) = 6n` (`∑ h = 0`), so `natDegree Rnum ≤ 6n + 1`
   (`PairPF.natDegree_Rnum_le`); every summand of `PFpoly` has `natDegree ≤ (6 - i) + 6n ≤ 6n + 5`
   (`PairPF.natDegree_PFpoly_le`).  Hence `natDegree Δ ≤ 6n + 5 < 6n + 6`.
2. *Local divisibility* (`PairPF.X_add_C_pow_dvd`): for each `k₀ ≤ n`, `(t + k₀)^6 ∣ Δ`.
   `PairPF.substPS a : ℚ[t] →+* ℚ⟦ε⟧` is the substitution `t ↦ a + ε`, and `substPS (-k₀) Δ` is
   the coercion of the polynomial `Δ.comp (X - C k₀)` (`PairPF.coe_comp_eq_substPS`).
   `PairPF.dvd_subst` shows `ε^6 ∣ substPS (-k₀) Δ`:
   * `substPS (-k₀) Rnum = (C (n - 2k₀) + C 2 · ε) · numSer n h (-k₀) = G_{k₀} · V`, with
     `V := ∏_{j≠k₀} (C (j - k₀) + ε)^6`; the inverse in `G_{k₀}` cancels against `V`
     (constant coefficient `∏_{j≠k₀} (j-k₀)^6 ≠ 0`).  No sign identities are needed, since
     `Gser` is defined directly through the shifted products.
   * `substPS (-k₀) PFpoly = T · V + E`, where `T := ∑_{i=1}^{6} r_{i,k₀} ε^{6-i}` and `ε^6 ∣ E`:
     every term with `k ≠ k₀` contains the factor `(t + k₀)^6 ↦ ε^6`.
   * `ε^6 ∣ G_{k₀} - T`: the coefficient of `ε^μ`, `μ < 6`, is `[ε^μ] G_{k₀} - r_{6-μ,k₀} = 0`.
   So the coefficients `< 6` of `Δ.comp (X - C k₀)` vanish, and composing back with `X + C k₀`
   gives `(X + C k₀)^6 ∣ Δ`.
3. *Coprimality.* The `(X + C k)^6`, `k ≤ n`, are pairwise coprime
   (`Polynomial.pairwise_coprime_X_sub_C`), so their product (monic, degree `6n + 6`) divides `Δ`
   (`Finset.prod_dvd_of_coprime`), and `Δ = 0` (`Polynomial.eq_zero_of_dvd_of_natDegree_lt`).

**Proof of `series`** (`PairPF.series_eq`).  Apply `PairPF.substPS y` to `poly`; the left side
becomes `(C (2y+n) + C 2 · ε) · numSer n h y`.  Multiply by the inverse of
`W := (∏_{j ≤ n} (C (y+j) + ε))^6` (constant coefficient `∏ (y+j)^6 ≠ 0`); each summand
`C r_{i,k} (C(y+k)+ε)^{6-i} ∏_{j≠k} (C(y+j)+ε)^6 · W⁻¹` equals `C r_{i,k} · ((C (y+k) + ε)^i)⁻¹`,
checked with `PowerSeries.eq_inv_iff_mul_eq_one` since `(C(y+k)+ε)^{6-i} (C(y+k)+ε)^i ∏_{j≠k} … = W`.

Adapted from `Zeta2Lean/Proofs/PartialFractions.lean` of the `{7,9,11}` repository (uniform
`(8,3)` family); the numerator, the pole order `6` and the degree count (which here needs
admissibility) differ.  Helper names live in the namespace `Zeta2.Pair.PairPF` and are `private`.

**Numerical check.** `python/pair_mirror.py`, section "Stmt_PF" (`poly` for `n ≤ 5`, `series` at
random rational `y`, random admissible `h`); `python/pair_audit_independent.py` checks the identity
at `6n + 6` points for 40 small admissible `(n, h)`.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Pair

namespace PairPF

/-! ### Elementary power-series identities -/

private lemma C_add_X_add_C (a b : ℚ) : (C a + X : PowerSeries ℚ) + C b = C (a + b) + X := by
  rw [map_add]; ring

/-! ### The substitution `t ↦ a + ε` -/

/-- The substitution `t ↦ a + ε`, as a ring hom `ℚ[t] →+* ℚ⟦ε⟧`. -/
private def substPS (a : ℚ) : Polynomial ℚ →+* PowerSeries ℚ :=
  Polynomial.eval₂RingHom (C : ℚ →+* PowerSeries ℚ) (C a + X)

private lemma substPS_X (a : ℚ) : substPS a Polynomial.X = C a + X := by
  simp [substPS]

private lemma substPS_C (a c : ℚ) : substPS a (Polynomial.C c) = C c := by
  simp [substPS]

private lemma substPS_X_add_C (a c : ℚ) :
    substPS a (Polynomial.X + Polynomial.C c) = C (a + c) + X := by
  rw [map_add, substPS_X, substPS_C, C_add_X_add_C]

/-- The linear factor: `(2t + n)(a + ε) = (2a + n) + 2ε`. -/
private lemma substPS_lin (n : ℕ) (a : ℚ) :
    substPS a (Polynomial.C 2 * Polynomial.X + Polynomial.C (n : ℚ)) =
      C (2 * a + n) + C 2 * X := by
  rw [map_add, map_mul, substPS_C, substPS_X, substPS_C, map_add, map_mul]
  ring

/-- The numerator product: `∏_m (a + ε + 1/2 - h_m)_{n + 2h_m} = numSer n h a`. -/
private lemma substPS_numProd (n : ℕ) (h : Fin 6 → ℤ) (a : ℚ) :
    substPS a (∏ m : Fin 6, ∏ u ∈ offsets n (h m),
      (Polynomial.X + Polynomial.C (1 / 2 + (u : ℚ)))) = numSer n h a := by
  unfold numSer
  rw [map_prod]
  refine Finset.prod_congr rfl (fun m _ => ?_)
  rw [map_prod]
  refine Finset.prod_congr rfl (fun u _ => ?_)
  rw [substPS_X_add_C, add_assoc]

/-! ### Local divisibility at a pole `-k₀` -/

/-- Key step: `ε^6 ∣ (Rnum - PFpoly)(-k₀ + ε)`. -/
private lemma dvd_subst (n : ℕ) (h : Fin 6 → ℤ) (k₀ : ℕ) (hk : k₀ ≤ n) :
    (X : PowerSeries ℚ) ^ 6 ∣ substPS (-(k₀ : ℚ)) (Rnum n h - PFpoly n h) := by
  have hmem : k₀ ∈ range (n + 1) := Finset.mem_range.2 (by omega)
  have hfac : ∀ c : ℚ,
      substPS (-(k₀ : ℚ)) (Polynomial.X + Polynomial.C c) = C (c - k₀) + X := by
    intro c
    rw [substPS_X_add_C, neg_add_eq_sub]
  have hX : (C ((k₀ : ℚ) - k₀) + X : PowerSeries ℚ) = X := by
    rw [sub_self, map_zero, zero_add]
  obtain ⟨V, hV⟩ : ∃ V : PowerSeries ℚ,
      V = ∏ j ∈ (range (n + 1)).erase k₀, (C ((j : ℚ) - k₀) + X) ^ 6 := ⟨_, rfl⟩
  obtain ⟨T, hT⟩ : ∃ T : PowerSeries ℚ,
      T = ∑ i ∈ Icc (1 : ℕ) 6, C (rcoef n h i k₀) * X ^ (6 - i) := ⟨_, rfl⟩
  obtain ⟨E, hE⟩ : ∃ E : PowerSeries ℚ,
      E = ∑ i ∈ Icc (1 : ℕ) 6, ∑ k ∈ (range (n + 1)).erase k₀,
        C (rcoef n h i k) * (C ((k : ℚ) - k₀) + X) ^ (6 - i) *
          ∏ j ∈ (range (n + 1)).erase k, (C ((j : ℚ) - k₀) + X) ^ 6 := ⟨_, rfl⟩
  have hV0 : constantCoeff V ≠ 0 := by
    rw [hV, map_prod, Finset.prod_ne_zero_iff]
    intro j hj
    have hj' : j ≠ k₀ := Finset.ne_of_mem_erase hj
    rw [map_pow, map_add, PowerSeries.constantCoeff_C, PowerSeries.constantCoeff_X, add_zero]
    exact pow_ne_zero _ (sub_ne_zero.2 (by exact_mod_cast hj'))
  -- the `Rnum` side: `Rnum(-k₀+ε) = G_{k₀}(ε) · V(ε)`
  have hR : substPS (-(k₀ : ℚ)) (Rnum n h) = Gser n h k₀ * V := by
    unfold Rnum Gser
    rw [← hV, map_mul, substPS_lin, substPS_numProd, mul_assoc _ V⁻¹ V,
      PowerSeries.inv_mul_cancel V hV0, mul_one,
      show (2 * -(k₀ : ℚ) + n) = n - 2 * k₀ by ring]
  -- the `PFpoly` side: the `k = k₀` terms give `T · V`, the others are divisible by `ε^6`
  have hPF : substPS (-(k₀ : ℚ)) (PFpoly n h) = T * V + E := by
    unfold PFpoly
    simp only [map_sum, map_mul, map_pow, map_prod, substPS_C, hfac]
    rw [hT, hE, hV, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [← Finset.add_sum_erase _ _ hmem, hX]
  -- `T` is the degree-`< 6` truncation of `G_{k₀}` (definition of `rcoef`)
  have hTdvd : (X : PowerSeries ℚ) ^ 6 ∣ Gser n h k₀ - T := by
    rw [PowerSeries.X_pow_dvd_iff]
    intro m hm
    rw [map_sub, hT, map_sum]
    simp only [PowerSeries.coeff_C_mul_X_pow]
    rw [Finset.sum_eq_single (6 - m)]
    · rw [ite_eq_left (by omega)]
      unfold rcoef
      rw [ite_eq_left ⟨by omega, by omega, hk⟩, Nat.sub_sub_self (by omega), sub_self]
    · intro i hi hne
      rw [Finset.mem_Icc] at hi
      rw [ite_eq_right (by omega)]
    · intro hnot
      exfalso; apply hnot; rw [Finset.mem_Icc]; omega
  have hEdvd : (X : PowerSeries ℚ) ^ 6 ∣ E := by
    rw [hE]
    apply Finset.dvd_sum
    intro i _
    apply Finset.dvd_sum
    intro k hk'
    have hk0 : k₀ ∈ (range (n + 1)).erase k :=
      Finset.mem_erase.2 ⟨(Finset.ne_of_mem_erase hk').symm, hmem⟩
    apply Dvd.dvd.mul_left
    have := Finset.dvd_prod_of_mem
      (fun j : ℕ => (C ((j : ℚ) - k₀) + X : PowerSeries ℚ) ^ 6) hk0
    simp only [hX] at this
    exact this
  rw [map_sub, hR, hPF]
  have hsplit : Gser n h k₀ * V - (T * V + E) = (Gser n h k₀ - T) * V - E := by ring
  rw [hsplit]
  exact dvd_sub (dvd_mul_of_dvd_left hTdvd V) hEdvd

/-- `substPS (-k₀) P` is the power series of the polynomial `P(t - k₀)`. -/
private lemma coe_comp_eq_substPS (k₀ : ℚ) (P : Polynomial ℚ) :
    ((P.comp (Polynomial.X - Polynomial.C k₀) : Polynomial ℚ) : PowerSeries ℚ) =
      substPS (-k₀) P := by
  have h : (Polynomial.coeToPowerSeries.ringHom).comp
      (Polynomial.compRingHom (Polynomial.X - Polynomial.C k₀)) = substPS (-k₀) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [substPS]
    · simp only [RingHom.comp_apply, Polynomial.coe_compRingHom_apply, Polynomial.X_comp,
        Polynomial.coeToPowerSeries.ringHom_apply, substPS_X]
      rw [Polynomial.coe_sub, Polynomial.coe_X, Polynomial.coe_C, map_neg]
      ring
  exact RingHom.congr_fun h P

/-- `(t + k₀)^6 ∣ Rnum - PFpoly` for every `k₀ ≤ n`. -/
private lemma X_add_C_pow_dvd (n : ℕ) (h : Fin 6 → ℤ) (k₀ : ℕ) (hk : k₀ ≤ n) :
    (Polynomial.X + Polynomial.C (k₀ : ℚ)) ^ 6 ∣ Rnum n h - PFpoly n h := by
  set P := Rnum n h - PFpoly n h with hP
  set Q := P.comp (Polynomial.X - Polynomial.C (k₀ : ℚ)) with hQ
  have hQdvd : Polynomial.X ^ 6 ∣ Q := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    have h1 := dvd_subst n h k₀ hk
    rw [← hP, ← coe_comp_eq_substPS, ← hQ, PowerSeries.X_pow_dvd_iff] at h1
    have h2 := h1 d hd
    rwa [Polynomial.coeff_coe] at h2
  obtain ⟨S, hS⟩ := hQdvd
  have hPQ : P = Q.comp (Polynomial.X + Polynomial.C (k₀ : ℚ)) := by
    rw [hQ, Polynomial.comp_assoc]
    simp
  refine ⟨S.comp (Polynomial.X + Polynomial.C (k₀ : ℚ)), ?_⟩
  rw [hPQ, hS, Polynomial.mul_comp, Polynomial.X_pow_comp]

/-! ### Degree bounds -/

/-- `card [-a, n + a) = n + 2a` when `n + 2a ≥ 0`. -/
private lemma card_offsets (n : ℕ) (a : ℤ) (ha : 0 ≤ (n : ℤ) + 2 * a) :
    ((offsets n a).card : ℤ) = n + 2 * a := by
  unfold offsets
  rw [Int.card_Ico, Int.toNat_of_nonneg (show (0 : ℤ) ≤ (n : ℤ) + a - -a by omega)]
  ring

/-- The numerator product has degree `≤ ∑_m (n + 2 h_m) = 6n`. -/
private lemma natDegree_numProd_le (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) :
    (∏ m : Fin 6, ∏ u ∈ offsets n (h m),
      (Polynomial.X + Polynomial.C (1 / 2 + (u : ℚ)))).natDegree ≤ 6 * n := by
  refine (Polynomial.natDegree_prod_le _ _).trans ?_
  have h3 : ∀ m : Fin 6, (∏ u ∈ offsets n (h m),
      (Polynomial.X + Polynomial.C (1 / 2 + (u : ℚ)))).natDegree ≤ (offsets n (h m)).card := by
    intro m
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun u _ => (Polynomial.natDegree_X_add_C _).le)).trans ?_
    simp
  refine (Finset.sum_le_sum (fun m _ => h3 m)).trans (le_of_eq ?_)
  have h4 : ((∑ m : Fin 6, (offsets n (h m)).card : ℕ) : ℤ) = ((6 * n : ℕ) : ℤ) := by
    rw [Nat.cast_sum, Finset.sum_congr rfl (fun m _ => card_offsets n (h m) (hh.len_nonneg m)),
      Finset.sum_add_distrib, ← Finset.mul_sum, hh.sum_eq]
    simp
  exact_mod_cast h4

private lemma natDegree_Rnum_le (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) :
    (Rnum n h).natDegree ≤ 6 * n + 1 := by
  unfold Rnum
  have h1 : (Polynomial.C (2 : ℚ) * Polynomial.X + Polynomial.C (n : ℚ)).natDegree ≤ 1 :=
    Polynomial.natDegree_linear_le
  have h2 := natDegree_numProd_le n h hh
  refine Polynomial.natDegree_mul_le.trans ?_
  omega

private lemma natDegree_PFpoly_le (n : ℕ) (h : Fin 6 → ℤ) :
    (PFpoly n h).natDegree ≤ 6 * n + 5 := by
  unfold PFpoly
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i hi
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro k hk
  rw [Finset.mem_Icc] at hi
  have hcard : ((range (n + 1)).erase k).card = n := by
    rw [Finset.card_erase_of_mem hk, Finset.card_range]; simp
  have h1 := (Polynomial.natDegree_mul_le (p := Polynomial.C (rcoef n h i k))
    (q := (Polynomial.X + Polynomial.C (k : ℚ)) ^ (6 - i)))
  rw [Polynomial.natDegree_C, zero_add] at h1
  have h2 := (Polynomial.natDegree_pow_le (p := Polynomial.X + Polynomial.C (k : ℚ)) (n := 6 - i))
  rw [Polynomial.natDegree_X_add_C, mul_one] at h2
  have h3 : (∏ j ∈ (range (n + 1)).erase k,
      (Polynomial.X + Polynomial.C (j : ℚ)) ^ 6).natDegree ≤ 6 * n := by
    refine (Polynomial.natDegree_prod_le _ _).trans ?_
    refine (Finset.sum_le_sum (fun j _ => (Polynomial.natDegree_pow_le (n := 6)).trans
      (by rw [Polynomial.natDegree_X_add_C]))).trans ?_
    rw [Finset.sum_const, smul_eq_mul, hcard, mul_one, mul_comm]
  refine Polynomial.natDegree_mul_le.trans ?_
  omega

/-! ### The two fields of `Stmt_PF` -/

private theorem poly_eq (n : ℕ) (h : Fin 6 → ℤ) (hh : Admissible n h) :
    Rnum n h = PFpoly n h := by
  have hdvd : ∏ k ∈ range (n + 1), (Polynomial.X + Polynomial.C (k : ℚ)) ^ 6 ∣
      Rnum n h - PFpoly n h := by
    apply Finset.prod_dvd_of_coprime
    · intro i _ j _ hij
      have hinj : Function.Injective (fun k : ℕ => -(k : ℚ)) := by
        intro a b hab
        simpa using hab
      have := Polynomial.pairwise_coprime_X_sub_C hinj hij
      simp only [Function.onFun, map_neg, sub_neg_eq_add] at this ⊢
      exact this.pow
    · intro k hk
      exact X_add_C_pow_dvd n h k (by simpa [Nat.lt_succ_iff] using hk)
  have hdeg : (Rnum n h - PFpoly n h).natDegree <
      (∏ k ∈ range (n + 1), (Polynomial.X + Polynomial.C (k : ℚ)) ^ 6).natDegree := by
    have hmon : ∀ k ∈ range (n + 1), ((Polynomial.X + Polynomial.C (k : ℚ)) ^ 6).Monic :=
      fun k _ => (Polynomial.monic_X_add_C _).pow 6
    rw [Polynomial.natDegree_prod_of_monic _ _ hmon]
    have h1 := Polynomial.natDegree_sub_le (Rnum n h) (PFpoly n h)
    have h2 := natDegree_Rnum_le n h hh
    have h3 := natDegree_PFpoly_le n h
    have h4 : ∑ i ∈ range (n + 1), ((Polynomial.X + Polynomial.C (i : ℚ)) ^ 6).natDegree =
        6 * (n + 1) := by
      rw [Finset.sum_congr rfl (fun k _ => by
        rw [(Polynomial.monic_X_add_C (k : ℚ)).natDegree_pow 6, Polynomial.natDegree_X_add_C])]
      rw [Finset.sum_const, smul_eq_mul, Finset.card_range, mul_one, mul_comm]
    rw [h4]
    omega
  exact sub_eq_zero.1 (Polynomial.eq_zero_of_dvd_of_natDegree_lt hdvd hdeg)

private theorem series_eq (n : ℕ) (h : Fin 6 → ℤ) (y : ℚ) (hh : Admissible n h)
    (hy : ∀ j ≤ n, y + (j : ℚ) ≠ 0) :
    Rser n h y = ∑ i ∈ Icc (1 : ℕ) 6, ∑ k ∈ range (n + 1),
      C (rcoef n h i k) * ((C (y + k) + X) ^ i)⁻¹ := by
  have hpoly := congrArg (substPS y) (poly_eq n h hh)
  have hF : ∀ c : ℚ, substPS y (Polynomial.X + Polynomial.C c) = C (y + c) + X :=
    substPS_X_add_C y
  have hF0 : ∀ j ∈ range (n + 1), constantCoeff (C (y + (j : ℚ)) + X : PowerSeries ℚ) ≠ 0 := by
    intro j hj
    rw [Finset.mem_range] at hj
    simpa using hy j (by omega)
  obtain ⟨W, hW⟩ : ∃ W : PowerSeries ℚ,
      W = (∏ j ∈ range (n + 1), (C (y + (j : ℚ)) + X)) ^ 6 := ⟨_, rfl⟩
  have hW0 : constantCoeff W ≠ 0 := by
    rw [hW, map_pow, map_prod]
    exact pow_ne_zero _ (Finset.prod_ne_zero_iff.2 hF0)
  have hLHS : Rser n h y = substPS y (Rnum n h) * W⁻¹ := by
    unfold Rser Rnum
    rw [map_mul, substPS_lin, substPS_numProd, hW]
  rw [hLHS, hpoly]
  unfold PFpoly
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  rw [Finset.mem_Icc] at hi
  rw [map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [map_mul, map_mul, substPS_C, map_pow (substPS y), hF, map_prod]
  simp_rw [map_pow (substPS y), hF]
  rw [mul_assoc, mul_assoc]
  congr 1
  have hFk : constantCoeff ((C (y + (k : ℚ)) + X) ^ i : PowerSeries ℚ) ≠ 0 := by
    rw [map_pow]; exact pow_ne_zero _ (hF0 k hk)
  rw [PowerSeries.eq_inv_iff_mul_eq_one hFk]
  have hWk : W = (C (y + (k : ℚ)) + X) ^ 6 *
      ∏ j ∈ (range (n + 1)).erase k, (C (y + (j : ℚ)) + X) ^ 6 := by
    rw [hW, ← Finset.prod_pow]
    exact (Finset.mul_prod_erase _
      (fun j : ℕ => (C (y + (j : ℚ)) + X : PowerSeries ℚ) ^ 6) hk).symm
  calc (C (y + (k : ℚ)) + X) ^ (6 - i) *
        ((∏ j ∈ (range (n + 1)).erase k, (C (y + (j : ℚ)) + X) ^ 6) * W⁻¹) *
        (C (y + (k : ℚ)) + X) ^ i
      = ((C (y + (k : ℚ)) + X) ^ (6 - i) * (C (y + (k : ℚ)) + X) ^ i *
          ∏ j ∈ (range (n + 1)).erase k, (C (y + (j : ℚ)) + X) ^ 6) * W⁻¹ := by ring
    _ = W * W⁻¹ := by rw [← pow_add, Nat.sub_add_cancel hi.2, hWk]
    _ = 1 := PowerSeries.mul_inv_cancel W hW0

end PairPF

theorem PF_proof : Stmt_PF := ⟨PairPF.poly_eq, PairPF.series_eq⟩

end Zeta2.Pair

end
