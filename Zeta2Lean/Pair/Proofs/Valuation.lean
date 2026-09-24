import Zeta2Lean.Pair.Statements

/-!
# GAP 4: 2-adic smallness `v₂(S_n) ≥ 12 n - O(log n)` (track pair79/valuation, Theorem G4)

gap: 'valuation' (GAP 4 of the pair programme; a proof obligation of `Pair/Main.lean`, not a
hypothesis).

**Task.** Prove `Stmt_Valuation` from `Stmt_IntegrandTaylor` (pair), `Stmt_Delta` and
`Stmt_DeltaFun` (reused from the `{7,9,11}` project): there are `c : ℝ`, `A : ℕ` such that for every
admissible `(n, h)` and every limit `I` of the Riemann sums of `integrand n h`,
`‖I‖ · 2^{12n} ≤ c (n+1)^A`.  (Unnormalised: `R_n` has no `2^{12n}` prefactor.)

**Status.** Complete, with `c = 6^10`, `A = 10`: `v₂(I) ≥ 12n - 10 ⌊log₂ 6n⌋` for every admissible
`(n, h)`.  `#print axioms Zeta2.Pair.Valuation_proof` gives `[propext, Classical.choice,
Quot.sound]`.  Used: `Stmt_Delta.{sumAll, smulAll, mulAll, monoAll, riemannAll}`,
`Stmt_DeltaFun.binom`; the exponent-6 analogue of `hcoefDelta` is re-proved here (`vgood_H6`).
Of `Admissible` only `∑ h_m = 0` and `n + 2 h_m ≥ 0` are used (no sign condition on the shifts).

**Informal proof** (Theorem G4 of `pair79/valuation/proof.md`, with a uniform logarithmic loss:
`L := ⌊log₂ 6n⌋ ≥ ⌊log₂ N_m⌋`, because `N_m := n + 2h_m ≤ 6n` by `∑ h = 0`, `N ≥ 0`).
1. *Product form.* By `Stmt_IntegrandTaylor`, `integrand n h x = -6 [ε³] R_n(x + 1/2 + ε)`, and
   `R_n(x + 1/2 + ε) = (2x+1+n+2ε) · ∏_m (T_m + ε)^{\underline{N_m}} · 2^{6n+6} H(2ε)`, where
   `(T + ε)^{\underline N} := ∏_{i<N} (T - i + ε)`, `H(δ) := ∏_{k≤n} (2x+2k+1+δ)^{-6}` and
   `T_m := x + n + h_m`.  The *top* `T_m` of every run is a natural number (`n + h_m ≥ n/2`), so
   no generalised binomial with a negative argument occurs (this disposes of the pitfall of
   runs `(x + 1 - h_m)_{N_m}` through non-positive integers).
2. *Vandermonde.* `(T+ε)^{\underline N} = ∑_{i+j=N} C(N,i) ε^{\underline i} T^{\underline j}`, so
   `[ε^μ] (T+ε)^{\underline N} = N! ∑_{i+j=N} s_{μ,i} C(T, j)`, `s_{μ,i} := [ε^μ] C(ε, i)`.
3. *Coefficients.* `C(ε, i) = (ε/i) ∏_{0<l<i} (ε/l - 1)` for `i ≥ 1`, hence (ultrametric
   inequality) `‖s_{μ,i}‖ ≤ 2^{μ ⌊log₂ i⌋}`.
4. *Δ-calculus on scaled Taylor coefficients.* Call `f : ℕ → ℚ₂` *good* if it is `ℤ₂`-valued with
   `Δ(f) ≥ -L`; good functions are closed under sums, products and multiplication by constants
   of norm `≤ 1` (`Stmt_Delta`).  An `x`-dependent power series `P_x(ε)` has *level* `E` if every
   `x ↦ 2^{jL - E} [ε^j] P_x(ε)` is good; levels add under products (`coeff_mul`).  Levels:
   * `2x+1+n+2ε`: `0` (`2x + 1 + n = C(x,1) + C(x+1+n,1)`, `Δ ≥ 0`);
   * the run of length `N_m`: `v₂(N_m!)` (steps 2–3 and `Δ(C(x + T', j)) ≥ -⌊log₂ j⌋`,
     `Stmt_DeltaFun.binom`, `j ≤ N_m ≤ 6n`);
   * `2^{6n+6} H(2ε)`: `6n + 6` (`[δ^β] H` is an integer polynomial in the `1/(2x+2k+1)`, whose
     `Δ ≥ 0`; `[ε^β] H(2ε) = 2^β [δ^β] H`).
   Hence `R_n(x + 1/2 + ε)` has level `E := 6n + 6 + ∑_m v₂(N_m!)`, i.e.
   `integrand n h = (-6 · 2^{E - 3L}) · g` with `g` good.
5. *Conclusion.* `Δ(integrand) ≥ E - 4L + 1` (`smulAll`, `‖-6‖ = 1/2`), so every Riemann sum has
   norm `≤ 2^{4L - E}` (`riemannAll`), and so has the limit `I` (`le_of_tendsto'`).  Legendre,
   `v₂(N!) = N - s₂(N) ≥ N - ⌊log₂ N⌋ - 1`, and `∑_m N_m = 6n` give `E ≥ 12n - 6L`; hence
   `‖I‖ 2^{12n} ≤ 2^{10L} ≤ (6n+1)^{10} ≤ 6^{10} (n+1)^{10}`.

**Lean proof map.**
* `VGood L f` ("good") and its closure lemmas `vgood_*`; `SerGood L E P` ("level `E`"),
  `serGood_mul`, `serGood_prod`, `serGood_mono`, `serGood_one`.
* Runs: `runPS`, `fallPS`, `val_vand` (Vandermonde, by induction with
  `Finset.sum_antidiagonal_choose_succ_mul`), `coeff_runPS`, `sco`, `norm_sco` (coefficient bounds
  `CBd` of products, `fall_succ_eq`), `serGood_run`.
* Linear factor: `serGood_lin`.  `H`-factor: `H6`, `val_H6_coeff`, `vgood_inv_odd`, `vgood_H6`
  (the sibling's `DeltaFunctions.lean` argument with exponent `6`), `serGood_H`.
* Product form: `offsets_prod` (the block `[-h, n+h)` is the run of length `n + 2h` ending at
  `x + n + h`), `val_den` (`(t + 1/2)_{n+1}^{-6} = 2^{6n+6} H(2ε)`), `val_Rser`.
* `val_legendre` (`sub_one_mul_padicValNat_factorial`); assembly in `Valuation_proof`.

**Numerical check.** `python/pair_mirror.py`, section "Stmt_Valuation (GAP 4)":
`max (12n - v₂(S_n))/log₂(n+1) ≤ 5.7` over all tested admissible `(n, h)`.  Configuration E has
`12n - v₂(S_n) ∈ [23, 41]` for `40 ≤ n ≤ 640`, inside the proved loss `10 ⌊log₂ 6n⌋` (e.g.
`n = 400`: proved `v₂(S_n) ≥ 4690`, true value `4763`).
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Pair

/-! ### 2-adic norm helpers -/

private lemma val_norm_two_zpow (z : ℤ) : ‖(2 : ℚ_[2]) ^ z‖ = (2 : ℝ) ^ (-z) := by
  have := Padic.norm_p_zpow (p := 2) z
  simpa using this

private lemma val_norm_natCast_le_one (a : ℕ) : ‖(a : ℚ_[2])‖ ≤ 1 := by
  have := Padic.norm_int_le_one (p := 2) (a : ℤ)
  simpa using this

private lemma val_norm_natCast (a : ℕ) (ha : a ≠ 0) :
    ‖(a : ℚ_[2])‖ = (2 : ℝ) ^ (-(padicValNat 2 a : ℤ)) := by
  rw [Padic.norm_eq_zpow_neg_valuation (by exact_mod_cast ha), Padic.valuation_natCast]
  norm_num

private lemma val_norm_inv_natCast_le (m : ℕ) (hm : m ≠ 0) :
    ‖((m : ℚ_[2]))⁻¹‖ ≤ (2 : ℝ) ^ (Nat.log 2 m : ℤ) := by
  rw [norm_inv, val_norm_natCast m hm, ← zpow_neg, neg_neg]
  apply zpow_le_zpow_right₀ (by norm_num)
  exact_mod_cast padicValNat_le_nat_log m

private lemma val_two_zpow_le_one {z : ℤ} (hz : z ≤ 0) : (2 : ℝ) ^ z ≤ 1 := by
  calc (2 : ℝ) ^ z ≤ (2 : ℝ) ^ (0 : ℤ) := zpow_le_zpow_right₀ (by norm_num) hz
    _ = 1 := zpow_zero 2

/-! ### `ℤ₂`-valued functions with `Δ ≥ -L` -/

/-- `ℤ₂`-valued with `Δ ≥ -L`. -/
private def VGood (L : ℕ) (f : ℕ → ℚ_[2]) : Prop :=
  IntValued f ∧ DeltaAll (-(L : ℤ)) f

private lemma vgood_congr {L : ℕ} {f g : ℕ → ℚ_[2]} (h : ∀ x, f x = g x) (hg : VGood L g) :
    VGood L f := by
  rw [show f = g from funext h]
  exact hg

private lemma vgood_const (L : ℕ) (a : ℚ_[2]) (ha : ‖a‖ ≤ 1) : VGood L (fun _ => a) := by
  refine ⟨fun _ => ha, fun k _ => ?_, ?_⟩
  · simp only [sub_self, norm_zero]
    positivity
  · exact ha.trans (one_le_zpow₀ (by norm_num) (by omega))

private lemma vgood_add (hD : Stmt_Delta) {L : ℕ} {f g : ℕ → ℚ_[2]} (hf : VGood L f)
    (hg : VGood L g) : VGood L (fun x => f x + g x) := by
  refine ⟨fun k => (Padic.nonarchimedean _ _).trans (max_le (hf.1 k) (hg.1 k)), ?_⟩
  have h := hD.sumAll (Finset.univ : Finset Bool) (fun b => if b then f else g) (-(L : ℤ))
    (by intro b _; cases b <;> simp [hf.2, hg.2])
  simpa [Fintype.sum_bool] using h

private lemma vgood_sum (hD : Stmt_Delta) {L : ℕ} {ι : Type} (s : Finset ι) (F : ι → ℕ → ℚ_[2])
    (h : ∀ i ∈ s, VGood L (F i)) : VGood L (fun x => ∑ i ∈ s, F i x) :=
  ⟨fun k => IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
      (fun i hi => (h i hi).1 k),
    hD.sumAll s F _ (fun i hi => (h i hi).2)⟩

private lemma vgood_mul (hD : Stmt_Delta) {L : ℕ} {f g : ℕ → ℚ_[2]} (hf : VGood L f)
    (hg : VGood L g) : VGood L (fun x => f x * g x) :=
  ⟨fun k => by
      rw [norm_mul]
      exact (mul_le_mul (hf.1 k) (hg.1 k) (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul 1)),
    hD.mulAll f g _ hf.1 hg.1 hf.2 hg.2⟩

private lemma vgood_smul (hD : Stmt_Delta) {L : ℕ} (a : ℚ_[2]) (ha : ‖a‖ ≤ 1) {f : ℕ → ℚ_[2]}
    (hf : VGood L f) : VGood L (fun x => a * f x) := by
  refine ⟨fun k => ?_, ?_⟩
  · rw [norm_mul]
    exact (mul_le_mul ha (hf.1 k) (norm_nonneg _) zero_le_one).trans (le_of_eq (one_mul 1))
  · have h := hD.smulAll f (-(L : ℤ)) 0 a (by simpa using ha) hf.2
    simpa using h

private lemma vgood_mono (hD : Stmt_Delta) {L L' : ℕ} (hL : L ≤ L') {f : ℕ → ℚ_[2]}
    (hf : VGood L f) : VGood L' f :=
  ⟨hf.1, hD.monoAll _ _ _ (by omega) hf.2⟩

private lemma vgood_pow (hD : Stmt_Delta) {L : ℕ} {f : ℕ → ℚ_[2]} (hf : VGood L f) (p : ℕ) :
    VGood L (fun x => f x ^ p) := by
  induction p with
  | zero => simpa using vgood_const L 1 (by simp)
  | succ p ih => simpa [pow_succ] using vgood_mul hD ih hf

private lemma vgood_prod (hD : Stmt_Delta) {L : ℕ} {ι : Type*} (s : Finset ι)
    (F : ι → ℕ → ℚ_[2]) (h : ∀ i ∈ s, VGood L (F i)) : VGood L (fun x => ∏ i ∈ s, F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using vgood_const L 1 (by simp)
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact vgood_mul hD (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

/-- `C(x + j, N)` with `⌊log₂ N⌋ ≤ L` (`Stmt_DeltaFun.binom`). -/
private lemma vgood_choose (hD : Stmt_Delta) (hDF : Stmt_DeltaFun) (j N L : ℕ)
    (hN : Nat.log 2 N ≤ L) : VGood L (fun x => ((Nat.choose (x + j) N : ℕ) : ℚ_[2])) :=
  ⟨fun _ => val_norm_natCast_le_one _, hD.monoAll _ _ _ (by omega) (hDF.binom j N)⟩

/-! ### Scaled Taylor coefficients -/

/-- The scaled Taylor coefficients `2^{jL - E} [ε^j] P_x(ε)` are `VGood L` (as functions of `x`). -/
private def SerGood (L : ℕ) (E : ℤ) (P : ℕ → PowerSeries ℚ) : Prop :=
  ∀ j : ℕ, VGood L (fun x => (2 : ℚ_[2]) ^ ((j : ℤ) * L - E) * ((coeff j (P x) : ℚ) : ℚ_[2]))

private lemma serGood_mono (hD : Stmt_Delta) {L : ℕ} {E E' : ℤ} (hE : E' ≤ E)
    {P : ℕ → PowerSeries ℚ} (hP : SerGood L E P) : SerGood L E' P := by
  intro j
  refine vgood_congr (fun x => ?_) (vgood_smul hD ((2 : ℚ_[2]) ^ (E - E')) ?_ (hP j))
  · rw [← mul_assoc, ← zpow_add₀ two_ne_zero]
    congr 2
    ring
  · rw [val_norm_two_zpow]
    exact val_two_zpow_le_one (by omega)

private lemma serGood_mul (hD : Stmt_Delta) {L : ℕ} {E E' : ℤ} {P Q : ℕ → PowerSeries ℚ}
    (hP : SerGood L E P) (hQ : SerGood L E' Q) : SerGood L (E + E') (fun x => P x * Q x) := by
  intro j
  refine vgood_congr (g := fun x => ∑ p ∈ antidiagonal j,
      ((2 : ℚ_[2]) ^ ((p.1 : ℤ) * L - E) * ((coeff p.1 (P x) : ℚ) : ℚ_[2])) *
      ((2 : ℚ_[2]) ^ ((p.2 : ℤ) * L - E') * ((coeff p.2 (Q x) : ℚ) : ℚ_[2]))) (fun x => ?_)
    (vgood_sum hD _ _ (fun p _ => vgood_mul hD (hP p.1) (hQ p.2)))
  rw [coeff_mul, Rat.cast_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  have e2 : (j : ℤ) * L - (E + E') = ((p.1 : ℤ) * L - E) + ((p.2 : ℤ) * L - E') := by
    rw [← hp]
    push_cast
    ring
  rw [e2, zpow_add₀ two_ne_zero, Rat.cast_mul]
  ring

private lemma serGood_one (L : ℕ) : SerGood L 0 (fun _ => 1) := by
  intro j
  by_cases hj : j = 0
  · subst hj
    exact vgood_congr (fun x => by simp) (vgood_const L 1 (by simp))
  · exact vgood_congr (fun x => by simp [coeff_one, hj]) (vgood_const L 0 (by simp))

private lemma serGood_prod (hD : Stmt_Delta) {L : ℕ} {ι : Type*} (s : Finset ι)
    (E : ι → ℤ) (P : ι → ℕ → PowerSeries ℚ) (h : ∀ i ∈ s, SerGood L (E i) (P i)) :
    SerGood L (∑ i ∈ s, E i) (fun x => ∏ i ∈ s, P i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using serGood_one L
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have e : (fun x => ∏ i ∈ insert a s, P i x) = fun x => P a x * ∏ i ∈ s, P i x := by
      funext x
      rw [Finset.prod_insert ha]
    rw [e]
    exact serGood_mul hD (h a (mem_insert_self a s)) (ih (fun i hi => h i (mem_insert_of_mem hi)))

/-! ### The linear factor `2x + 1 + n + 2ε` -/

private lemma serGood_lin (hD : Stmt_Delta) (hDF : Stmt_DeltaFun) (n L : ℕ) :
    SerGood L 0 (fun x => C (((2 * x + 1 + n : ℕ) : ℚ)) + C 2 * X) := by
  intro j
  rcases j with _ | _ | j
  · refine vgood_congr (g := fun x => ((Nat.choose (x + 0) 1 : ℕ) : ℚ_[2]) +
      ((Nat.choose (x + (1 + n)) 1 : ℕ) : ℚ_[2])) (fun x => ?_)
      (vgood_add hD (vgood_choose hD hDF 0 1 L (by simp))
        (vgood_choose hD hDF (1 + n) 1 L (by simp)))
    rw [map_add, coeff_C, coeff_C_mul, coeff_X]
    simp only [Nat.choose_one_right, ite_true, zero_ne_one, ite_false, mul_zero, add_zero,
      Nat.cast_zero, zero_mul, sub_zero, zpow_zero, one_mul]
    push_cast
    ring
  · refine vgood_congr (g := fun _ => (2 : ℚ_[2]) ^ ((L : ℤ) + 1)) (fun x => ?_)
      (vgood_const L _ ?_)
    · rw [map_add, coeff_C, coeff_C_mul, coeff_X]
      simp only [one_ne_zero, ite_false, ite_true, zero_add, mul_one, Nat.cast_one, one_mul,
        sub_zero, Rat.cast_ofNat]
      rw [zpow_add₀ two_ne_zero, zpow_one]
    · rw [val_norm_two_zpow]
      exact val_two_zpow_le_one (by omega)
  · refine vgood_congr (g := fun _ => (0 : ℚ_[2])) (fun x => ?_) (vgood_const L 0 (by simp))
    rw [map_add, coeff_C, coeff_C_mul, coeff_X]
    simp

/-! ### Runs of consecutive factors: Vandermonde -/

/-- `ε (ε - 1) ⋯ (ε - k + 1)`. -/
private def fallPS (k : ℕ) : PowerSeries ℚ :=
  ∏ i ∈ range k, (X - C (i : ℚ))

/-- `(T + ε) (T - 1 + ε) ⋯ (T - N + 1 + ε)`. -/
private def runPS (T N : ℕ) : PowerSeries ℚ :=
  ∏ i ∈ range N, (C ((T : ℚ) - i) + X)

private lemma runPS_succ (T N : ℕ) : runPS T (N + 1) = runPS T N * (C ((T : ℚ) - N) + X) := by
  unfold runPS
  rw [prod_range_succ]

private lemma fallPS_succ (k : ℕ) : fallPS (k + 1) = fallPS k * (X - C (k : ℚ)) := by
  unfold fallPS
  rw [prod_range_succ]

private lemma val_desc_succ (T m : ℕ) :
    ((T.descFactorial (m + 1) : ℕ) : ℚ) = ((T : ℚ) - m) * ((T.descFactorial m : ℕ) : ℚ) := by
  rw [Nat.descFactorial_succ]
  rcases le_or_gt m T with hmT | hmT
  · rw [Nat.cast_mul, Nat.cast_sub hmT]
  · rw [Nat.descFactorial_eq_zero_iff_lt.2 hmT]
    simp

/-- Vandermonde: `(T + ε)^{\underline N} = ∑_{i+j=N} C(N,i) ε^{\underline i} T^{\underline j}`. -/
private lemma val_vand (T N : ℕ) :
    runPS T N = ∑ ij ∈ antidiagonal N,
      ((N.choose ij.1 : ℕ) : PowerSeries ℚ) *
        (fallPS ij.1 * C ((T.descFactorial ij.2 : ℕ) : ℚ)) := by
  induction N with
  | zero => simp [runPS, fallPS]
  | succ N ih =>
    have hs : (∑ ij ∈ antidiagonal (N + 1), (((N + 1).choose ij.1 : ℕ) : PowerSeries ℚ) *
        (fallPS ij.1 * C ((T.descFactorial ij.2 : ℕ) : ℚ))) =
        (∑ ij ∈ antidiagonal N, ((N.choose ij.1 : ℕ) : PowerSeries ℚ) *
          (fallPS ij.1 * C ((T.descFactorial (ij.2 + 1) : ℕ) : ℚ))) +
        ∑ ij ∈ antidiagonal N, ((N.choose ij.2 : ℕ) : PowerSeries ℚ) *
          (fallPS (ij.1 + 1) * C ((T.descFactorial ij.2 : ℕ) : ℚ)) :=
      Finset.sum_antidiagonal_choose_succ_mul
        (fun i j => fallPS i * C ((T.descFactorial j : ℕ) : ℚ)) N
    rw [hs, runPS_succ, ih, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hij
    rw [← Nat.choose_symm_of_eq_add hij.symm, fallPS_succ, val_desc_succ]
    have hN : C ((T : ℚ) - (N : ℕ)) = C ((T : ℚ) - (ij.2 : ℕ)) - C ((ij.1 : ℕ) : ℚ) := by
      rw [← map_sub]
      congr 1
      rw [← hij]
      push_cast
      ring
    rw [hN, map_mul]
    ring

/-- `s μ k = [ε^μ] C(ε, k)`. -/
private def sco (μ k : ℕ) : ℚ :=
  coeff μ (fallPS k) / (k.factorial : ℚ)

private lemma coeff_natCast_mul' (a : ℕ) (F : PowerSeries ℚ) (μ : ℕ) :
    coeff μ ((a : PowerSeries ℚ) * F) = (a : ℚ) * coeff μ F := by
  rw [← map_natCast (C : ℚ →+* PowerSeries ℚ) a, coeff_C_mul]

/-- `[ε^μ] (T + ε)^{\underline N} = N! ∑_{i+j=N} [ε^μ] C(ε, i) · C(T, j)`. -/
private lemma coeff_runPS (T N μ : ℕ) :
    coeff μ (runPS T N) =
      ∑ ij ∈ antidiagonal N, (N.factorial : ℚ) * sco μ ij.1 * (T.choose ij.2 : ℚ) := by
  rw [val_vand, map_sum]
  refine Finset.sum_congr rfl fun ij hij => ?_
  rw [HasAntidiagonal.mem_antidiagonal] at hij
  rw [coeff_natCast_mul', coeff_mul_C, sco, Nat.descFactorial_eq_factorial_mul_choose]
  have h1 := Nat.choose_mul_factorial_mul_factorial (show ij.1 ≤ N by omega)
  rw [show N - ij.1 = ij.2 by omega] at h1
  have hf : (ij.1.factorial : ℚ) ≠ 0 := by positivity
  rw [← h1]
  push_cast
  field_simp

/-! ### Coefficient bounds for `[ε^μ] C(ε, k)` -/

/-- `‖[ε^j] F‖ ≤ 2^{jL}` for all `j`. -/
private def CBd (L : ℕ) (F : PowerSeries ℚ) : Prop :=
  ∀ j : ℕ, ‖((coeff j F : ℚ) : ℚ_[2])‖ ≤ (2 : ℝ) ^ ((j : ℤ) * L)

private lemma cbd_mul {L : ℕ} {F G : PowerSeries ℚ} (hF : CBd L F) (hG : CBd L G) :
    CBd L (F * G) := by
  intro j
  rw [coeff_mul, Rat.cast_sum]
  apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg (by positivity)
  intro p hp
  rw [HasAntidiagonal.mem_antidiagonal] at hp
  rw [Rat.cast_mul, norm_mul]
  calc _ ≤ (2 : ℝ) ^ ((p.1 : ℤ) * L) * (2 : ℝ) ^ ((p.2 : ℤ) * L) :=
        mul_le_mul (hF p.1) (hG p.2) (norm_nonneg _) (by positivity)
    _ = (2 : ℝ) ^ ((j : ℤ) * L) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← hp]
        push_cast
        ring_nf

private lemma cbd_one (L : ℕ) : CBd L 1 := by
  intro j
  rw [coeff_one]
  split_ifs with h
  · subst h
    simp
  · simp only [Rat.cast_zero, norm_zero]
    positivity

private lemma cbd_prod {L : ℕ} {ι : Type*} (s : Finset ι) (F : ι → PowerSeries ℚ)
    (h : ∀ i ∈ s, CBd L (F i)) : CBd L (∏ i ∈ s, F i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cbd_one L
  | insert a s ha ih =>
    rw [prod_insert ha]
    exact cbd_mul (h a (mem_insert_self a s)) (ih fun i hi => h i (mem_insert_of_mem hi))

private lemma cbd_lin {L : ℕ} (c d : ℚ) (hc : ‖((c : ℚ) : ℚ_[2])‖ ≤ (2 : ℝ) ^ (L : ℤ))
    (hd : ‖((d : ℚ) : ℚ_[2])‖ ≤ 1) : CBd L (C c * X + C d) := by
  intro j
  rcases j with _ | _ | j
  · simpa [coeff_X, coeff_C] using hd
  · simpa [coeff_X, coeff_C] using hc
  · simp only [map_add, coeff_succ_mul_X, coeff_succ_C, add_zero, Rat.cast_zero, norm_zero]
    positivity

private lemma fall_succ_eq (k : ℕ) :
    fallPS (k + 1) = C (((k + 1).factorial : ℕ) : ℚ) *
      ((C (1 / ((k : ℚ) + 1)) * X + C 0) *
        ∏ i ∈ range k, (C (1 / ((i : ℚ) + 1)) * X + C (-1))) := by
  have hfac : ∀ i : ℕ, (X - C (((i + 1 : ℕ) : ℚ)) : PowerSeries ℚ) =
      C ((i : ℚ) + 1) * (C (1 / ((i : ℚ) + 1)) * X + C (-1)) := by
    intro i
    have hi : ((i : ℚ) + 1) ≠ 0 := by positivity
    have e1 : C ((i : ℚ) + 1) * C (1 / ((i : ℚ) + 1)) = (1 : PowerSeries ℚ) := by
      rw [← map_mul, mul_one_div_cancel hi, map_one]
    have e2 : C ((i : ℚ) + 1) * C (-1 : ℚ) = -C (((i + 1 : ℕ) : ℚ)) := by
      rw [← map_mul, ← map_neg]
      congr 1
      push_cast
      ring
    rw [mul_add, ← mul_assoc, e1, one_mul, e2, sub_eq_add_neg]
  unfold fallPS
  rw [prod_range_succ', Finset.prod_congr rfl (fun i _ => hfac i), prod_mul_distrib, ← map_prod]
  have hk : ((k : ℚ) + 1) ≠ 0 := by positivity
  have hprod : ∏ i ∈ range k, ((i : ℚ) + 1) = ((k.factorial : ℕ) : ℚ) := by
    rw [← Finset.prod_range_add_one_eq_factorial]
    push_cast
    rfl
  rw [hprod, Nat.factorial_succ]
  simp only [Nat.cast_zero, map_zero, sub_zero, add_zero]
  push_cast
  rw [map_mul]
  have e : C ((k : ℚ) + 1) * C (1 / ((k : ℚ) + 1)) = (1 : PowerSeries ℚ) := by
    rw [← map_mul, mul_one_div_cancel hk, map_one]
  linear_combination (C ((k.factorial : ℕ) : ℚ) * X *
    ∏ i ∈ range k, (C (1 / ((i : ℚ) + 1)) * X + C (-1))) * e.symm

private lemma sco_succ (μ k : ℕ) :
    sco μ (k + 1) = coeff μ ((C (1 / ((k : ℚ) + 1)) * X + C 0) *
      ∏ i ∈ range k, (C (1 / ((i : ℚ) + 1)) * X + C (-1))) := by
  rw [sco, fall_succ_eq, coeff_C_mul]
  have : (((k + 1).factorial : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp

/-- `‖[ε^μ] C(ε, k)‖ ≤ 2^{μ ⌊log₂ k⌋}`. -/
private lemma norm_sco (μ k : ℕ) :
    ‖((sco μ k : ℚ) : ℚ_[2])‖ ≤ (2 : ℝ) ^ ((μ : ℤ) * Nat.log 2 k) := by
  rcases k with _ | k
  · simp only [sco, fallPS, range_zero, prod_empty, coeff_one, Nat.factorial_zero, Nat.cast_one,
      div_one, Nat.log_zero_right, Nat.cast_zero, mul_zero, zpow_zero]
    split_ifs <;> simp
  · rw [sco_succ]
    have hinv : ∀ m : ℕ, m ≤ k →
        ‖(((1 / ((m : ℚ) + 1)) : ℚ) : ℚ_[2])‖ ≤ (2 : ℝ) ^ ((Nat.log 2 (k + 1) : ℕ) : ℤ) := by
      intro m hmk
      have e : (((1 / ((m : ℚ) + 1)) : ℚ) : ℚ_[2]) = (((m + 1 : ℕ) : ℚ_[2]))⁻¹ := by
        push_cast
        ring
      rw [e]
      refine (val_norm_inv_natCast_le (m + 1) (by omega)).trans ?_
      apply zpow_le_zpow_right₀ (by norm_num)
      exact_mod_cast Nat.log_mono_right (by omega : m + 1 ≤ k + 1)
    have hB : CBd (Nat.log 2 (k + 1)) ((C (1 / ((k : ℚ) + 1)) * X + C 0) *
        ∏ i ∈ range k, (C (1 / ((i : ℚ) + 1)) * X + C (-1))) := by
      apply cbd_mul
      · exact cbd_lin _ _ (hinv k le_rfl) (by simp)
      · apply cbd_prod
        intro i hi
        rw [Finset.mem_range] at hi
        exact cbd_lin _ _ (hinv i (by omega)) (by simp)
    exact hB μ

/-! ### A run `(T + ε)^{\underline N}`, `T = x + j`: `SerGood` with `E = v₂(N!)` -/

private lemma serGood_run (hD : Stmt_Delta) (hDF : Stmt_DeltaFun) (j N L : ℕ)
    (hNL : Nat.log 2 N ≤ L) :
    SerGood L (padicValNat 2 N.factorial : ℤ) (fun x => runPS (x + j) N) := by
  intro μ
  have hNf : N.factorial ≠ 0 := Nat.factorial_ne_zero N
  refine vgood_congr (g := fun x => ∑ ij ∈ antidiagonal N,
      ((2 : ℚ_[2]) ^ (-(padicValNat 2 N.factorial : ℤ)) * ((N.factorial : ℕ) : ℚ_[2])) *
      (((2 : ℚ_[2]) ^ ((μ : ℤ) * L) * ((sco μ ij.1 : ℚ) : ℚ_[2])) *
        ((Nat.choose (x + j) ij.2 : ℕ) : ℚ_[2]))) (fun x => ?_) ?_
  · rw [coeff_runPS, Rat.cast_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ij _ => ?_
    rw [sub_eq_add_neg, zpow_add₀ two_ne_zero]
    push_cast
    ring
  · refine vgood_sum hD _ _ fun ij hij => ?_
    rw [HasAntidiagonal.mem_antidiagonal] at hij
    refine vgood_smul hD _ ?_ (vgood_smul hD _ ?_ (vgood_choose hD hDF j ij.2 L ?_))
    · rw [norm_mul, val_norm_two_zpow, val_norm_natCast _ hNf, neg_neg,
        ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), add_neg_cancel, zpow_zero]
    · rw [norm_mul, val_norm_two_zpow]
      have hlog : (μ : ℤ) * (Nat.log 2 ij.1 : ℤ) ≤ (μ : ℤ) * L := by
        have : Nat.log 2 ij.1 ≤ L := (Nat.log_mono_right (by omega)).trans hNL
        exact mul_le_mul_of_nonneg_left (by exact_mod_cast this) (by positivity)
      calc (2 : ℝ) ^ (-((μ : ℤ) * L)) * ‖((sco μ ij.1 : ℚ) : ℚ_[2])‖
          ≤ (2 : ℝ) ^ (-((μ : ℤ) * L)) * (2 : ℝ) ^ ((μ : ℤ) * L) := by
            gcongr
            exact (norm_sco μ ij.1).trans (zpow_le_zpow_right₀ (by norm_num) hlog)
        _ = 1 := by rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), neg_add_cancel, zpow_zero]
    · exact (Nat.log_mono_right (by omega)).trans hNL

/-! ### The factor `∏_{k ≤ n} (2x + 2k + 1 + 2ε)^{-6}` (exponent-6 analogue of `hcoefDelta`) -/

/-- `H(δ) = ∏_{k ≤ n} (2x + 2k + 1 + δ)^{-6}`. -/
private def H6 (n x : ℕ) : PowerSeries ℚ :=
  ∏ k ∈ range (n + 1), ((C (((2 * x + 2 * k + 1 : ℕ) : ℚ)) + X) ^ 6)⁻¹

/-- `(C u + X)⁻¹ = ∑_j (-1)^j u^{-(j+1)} X^j`. -/
private lemma val_inv_C_add_X (u : ℚ) (hu : u ≠ 0) :
    (C u + X : PowerSeries ℚ)⁻¹ = PowerSeries.mk (fun j => (-1) ^ j * u⁻¹ ^ (j + 1)) := by
  rw [PowerSeries.inv_eq_iff_mul_eq_one (by simp [hu])]
  ext n
  rcases n with _ | n
  · simp [hu]
  · rw [mul_add, map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X]
    simp only [PowerSeries.coeff_mk, PowerSeries.coeff_one, Nat.succ_ne_zero, ite_false]
    have h : u * u⁻¹ = 1 := mul_inv_cancel₀ hu
    linear_combination (-(-1) ^ n * u⁻¹ ^ (n + 1)) * h

/-- `[δ^β] H` as an explicit polynomial in the `(2x+2k+1)^{-1}` with integer coefficients. -/
private lemma val_H6_coeff (n β x : ℕ) :
    coeff β (H6 n x) = ∑ l ∈ (range (n + 1)).finsuppAntidiag β, ∏ k ∈ range (n + 1),
      ∑ l' ∈ (range 6).finsuppAntidiag (l k), ∏ i ∈ range 6,
        ((-1 : ℚ) ^ (l' i) * ((((2 * x + 2 * k + 1 : ℕ) : ℚ))⁻¹) ^ (l' i + 1)) := by
  unfold H6
  have h : ∀ k ∈ range (n + 1), ((C (((2 * x + 2 * k + 1 : ℕ) : ℚ)) + X) ^ 6)⁻¹ =
      (PowerSeries.mk (fun j => (-1) ^ j * (((2 * x + 2 * k + 1 : ℕ) : ℚ))⁻¹ ^ (j + 1))) ^ 6 := by
    intro k _
    rw [← PowerSeries.inv_pow, val_inv_C_add_X _ (by positivity)]
  rw [Finset.prod_congr rfl h, PowerSeries.coeff_prod]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.prod_congr rfl
  intro k _
  rw [PowerSeries.coeff_pow]
  simp only [PowerSeries.coeff_mk]

private lemma val_norm_odd (a : ℕ) (ha : Odd a) : ‖(a : ℚ_[2])‖ = 1 := by
  rw [Padic.norm_natCast_eq_one_iff]
  exact Nat.coprime_two_left.mpr ha

private lemma vgood_inv_odd (k : ℕ) :
    VGood 0 (fun x => (((2 * x + 2 * k + 1 : ℕ) : ℚ_[2]))⁻¹) := by
  have hodd : ∀ x : ℕ, ‖((2 * x + 2 * k + 1 : ℕ) : ℚ_[2])‖ = 1 := fun x =>
    val_norm_odd _ ⟨x + k, by ring⟩
  refine ⟨fun x => by rw [norm_inv, hodd x, inv_one], ?_, ?_⟩
  · intro y hy
    have hy0 : y ≠ 0 := by
      have : 1 ≤ y := by simpa using hy
      omega
    have hL : 2 ^ Nat.log 2 y ≤ y := Nat.pow_log_le_self 2 hy0
    set L := Nat.log 2 y with hLdef
    have hB : ((2 * y + 2 * k + 1 : ℕ) : ℚ_[2]) =
        ((2 * (y - 2 ^ L) + 2 * k + 1 : ℕ) : ℚ_[2]) + 2 * 2 ^ L := by
      have : 2 * y + 2 * k + 1 = (2 * (y - 2 ^ L) + 2 * k + 1) + 2 * 2 ^ L := by omega
      rw [this]
      push_cast
      ring
    have hA1 := hodd (y - 2 ^ L)
    have hB1 := hodd y
    have hA0 : ((2 * (y - 2 ^ L) + 2 * k + 1 : ℕ) : ℚ_[2]) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hA1
      exact zero_ne_one hA1
    have hB0 : ((2 * y + 2 * k + 1 : ℕ) : ℚ_[2]) ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hB1
      exact zero_ne_one hB1
    change ‖(((2 * y + 2 * k + 1 : ℕ) : ℚ_[2]))⁻¹ -
      (((2 * (y - 2 ^ L) + 2 * k + 1 : ℕ) : ℚ_[2]))⁻¹‖ ≤ _
    rw [inv_sub_inv hB0 hA0, norm_div, norm_mul, hA1, hB1, hB]
    have : ((2 * (y - 2 ^ L) + 2 * k + 1 : ℕ) : ℚ_[2]) -
        (((2 * (y - 2 ^ L) + 2 * k + 1 : ℕ) : ℚ_[2]) + 2 * 2 ^ L) = -(2 : ℚ_[2]) ^ (L + 1) := by
      ring
    rw [this, norm_neg, ← zpow_natCast, val_norm_two_zpow, mul_one, div_one]
    apply zpow_le_zpow_right₀ (by norm_num)
    push_cast
    omega
  · rw [norm_inv, hodd 0, inv_one]
    exact one_le_zpow₀ (by norm_num) (by norm_num)

private lemma vgood_H6 (hD : Stmt_Delta) (n β : ℕ) :
    VGood 0 (fun x => ((coeff β (H6 n x) : ℚ) : ℚ_[2])) := by
  have hfun : ∀ x, ((coeff β (H6 n x) : ℚ) : ℚ_[2]) =
      ∑ l ∈ (range (n + 1)).finsuppAntidiag β, ∏ k ∈ range (n + 1),
        ∑ l' ∈ (range 6).finsuppAntidiag (l k), ∏ i ∈ range 6,
          ((-1 : ℚ_[2]) ^ (l' i) * (((2 * x + 2 * k + 1 : ℕ) : ℚ_[2]))⁻¹ ^ (l' i + 1)) := by
    intro x
    rw [val_H6_coeff]
    push_cast
    rfl
  refine vgood_congr hfun ?_
  refine vgood_sum hD _ _ (fun l _ => ?_)
  refine vgood_prod hD _ _ (fun k _ => ?_)
  refine vgood_sum hD _ _ (fun l' _ => ?_)
  refine vgood_prod hD _ _ (fun i _ => ?_)
  exact vgood_mul hD (vgood_const 0 _ (by simp)) (vgood_pow hD (vgood_inv_odd k) _)

private lemma val_norm_two_pow_le_one (m : ℕ) : ‖(2 : ℚ_[2]) ^ m‖ ≤ 1 := by
  rw [← zpow_natCast, val_norm_two_zpow]
  exact val_two_zpow_le_one (by omega)

private lemma serGood_H (hD : Stmt_Delta) (n L : ℕ) :
    SerGood L ((6 * n + 6 : ℕ) : ℤ) (fun x => C ((2 : ℚ) ^ (6 * n + 6)) * rescale 2 (H6 n x)) := by
  intro j
  refine vgood_congr (g := fun x => (2 : ℚ_[2]) ^ (j * L + j) * ((coeff j (H6 n x) : ℚ) : ℚ_[2]))
    (fun x => ?_) (vgood_smul hD _ (val_norm_two_pow_le_one _)
      (vgood_mono hD (Nat.zero_le L) (vgood_H6 hD n j)))
  rw [coeff_C_mul, coeff_rescale]
  push_cast
  rw [← zpow_natCast (2 : ℚ_[2]) (6 * n + 6), ← zpow_natCast (2 : ℚ_[2]) j,
    ← zpow_natCast (2 : ℚ_[2]) (j * L + j), ← mul_assoc, ← mul_assoc, ← zpow_add₀ two_ne_zero,
    ← zpow_add₀ two_ne_zero]
  congr 2
  push_cast
  ring

/-! ### Product form of `R_n(x + 1/2 + ε)` -/

private lemma val_rescale_C (a r : ℚ) : rescale a (C r) = C r := by
  ext n
  simp only [coeff_rescale, coeff_C]
  split_ifs with h
  · subst h
    simp
  · simp

private lemma val_rescale_lin (c : ℚ) : rescale (2 : ℚ) (C c + X) = C c + C 2 * X := by
  rw [map_add, val_rescale_C, rescale_X]

/-- `(t + 1/2)_{n+1}^{-6}` at `t = x + ε`: `2^{6n+6} H(2ε)`. -/
private lemma val_den (n x : ℕ) :
    ((∏ j ∈ range (n + 1), (C ((x : ℚ) + 1 / 2 + j) + X)) ^ 6)⁻¹ =
      C ((2 : ℚ) ^ (6 * n + 6)) * rescale 2 (H6 n x) := by
  have hφ : ∀ k : ℕ, constantCoeff ((C (((2 * x + 2 * k + 1 : ℕ) : ℚ)) + X) ^ 6) ≠ 0 := by
    intro k
    simp only [map_pow, map_add, constantCoeff_C, constantCoeff_X, add_zero]
    positivity
  have hDen : (∏ j ∈ range (n + 1), (C ((x : ℚ) + 1 / 2 + j) + X)) ^ 6 =
      C (((1 : ℚ) / 2) ^ (6 * n + 6)) *
        rescale 2 (∏ k ∈ range (n + 1), (C (((2 * x + 2 * k + 1 : ℕ) : ℚ)) + X) ^ 6) := by
    have hj : ∀ j ∈ range (n + 1), (C ((x : ℚ) + 1 / 2 + j) + X) ^ 6 =
        C (((1 : ℚ) / 2) ^ 6) * rescale 2 ((C (((2 * x + 2 * j + 1 : ℕ) : ℚ)) + X) ^ 6) := by
      intro j _
      rw [map_pow (rescale (2 : ℚ)), val_rescale_lin, map_pow C, ← mul_pow]
      congr 1
      have e1 : (1 / 2 : ℚ) * ((2 * x + 2 * j + 1 : ℕ) : ℚ) = (x : ℚ) + 1 / 2 + j := by
        push_cast
        ring
      have e2 : (1 / 2 : ℚ) * 2 = 1 := by norm_num
      rw [mul_add, ← mul_assoc, ← map_mul, ← map_mul, e1, e2, map_one, one_mul]
    rw [map_prod, ← Finset.prod_pow, Finset.prod_congr rfl hj, Finset.prod_mul_distrib,
      Finset.prod_const, card_range, ← map_pow, ← pow_mul, show 6 * (n + 1) = 6 * n + 6 by ring]
  symm
  rw [PowerSeries.eq_inv_iff_mul_eq_one]
  · rw [hDen]
    calc C ((2 : ℚ) ^ (6 * n + 6)) * rescale 2 (H6 n x) *
          (C (((1 : ℚ) / 2) ^ (6 * n + 6)) *
            rescale 2 (∏ k ∈ range (n + 1), (C (((2 * x + 2 * k + 1 : ℕ) : ℚ)) + X) ^ 6))
        = C ((2 : ℚ) ^ (6 * n + 6) * ((1 : ℚ) / 2) ^ (6 * n + 6)) *
            rescale 2 (H6 n x *
              ∏ k ∈ range (n + 1), (C (((2 * x + 2 * k + 1 : ℕ) : ℚ)) + X) ^ 6) := by
          rw [map_mul, map_mul]
          ring
      _ = 1 := by
          rw [← mul_pow, show (2 : ℚ) * (1 / 2) = 1 by norm_num, one_pow, map_one, one_mul]
          unfold H6
          rw [← Finset.prod_mul_distrib,
            Finset.prod_eq_one (fun k _ => PowerSeries.inv_mul_cancel _ (hφ k)), map_one]
  · rw [map_pow, map_prod]
    apply pow_ne_zero
    rw [Finset.prod_ne_zero_iff]
    intro j _
    simp only [map_add, constantCoeff_C, constantCoeff_X, add_zero]
    positivity

/-- A numerator block `∏_{u ∈ [-a, n+a)} (x + 1 + u + ε)` is the run of length `n + 2a` ending at
`x + n + a ≥ 0`. -/
private lemma offsets_prod (n x : ℕ) (a : ℤ) (ha : 0 ≤ (n : ℤ) + 2 * a) :
    ∏ u ∈ offsets n a, (C ((x : ℚ) + 1 / 2 + 1 / 2 + (u : ℚ)) + X) =
      runPS (x + ((n : ℤ) + a).toNat) (((n : ℤ) + 2 * a).toNat) := by
  have hna : 0 ≤ (n : ℤ) + a := by omega
  unfold offsets runPS
  symm
  refine Finset.prod_nbij' (fun i : ℕ => (n : ℤ) + a - 1 - i)
    (fun u : ℤ => ((n : ℤ) + a - 1 - u).toNat) ?_ ?_ ?_ ?_ ?_
  · intro i hi
    rw [Finset.mem_range] at hi
    rw [Finset.mem_Ico]
    omega
  · intro u hu
    rw [Finset.mem_Ico] at hu
    rw [Finset.mem_range]
    omega
  · intro i hi
    omega
  · intro u hu
    rw [Finset.mem_Ico] at hu
    omega
  · intro i hi
    have e1 : ((((n : ℤ) + a).toNat : ℕ) : ℚ) = (n : ℚ) + (a : ℚ) := by
      have h1 : ((((n : ℤ) + a).toNat : ℕ) : ℤ) = (n : ℤ) + a := Int.toNat_of_nonneg hna
      have h2 : ((((n : ℤ) + a).toNat : ℕ) : ℚ) = (((((n : ℤ) + a).toNat : ℕ) : ℤ) : ℚ) := by
        norm_cast
      rw [h2, h1]
      push_cast
      ring
    congr 2
    rw [Nat.cast_add, e1]
    push_cast
    ring

/-- `R_n(x + 1/2 + ε) = (2x+1+n+2ε) · ∏_m (x + n + h_m + ε)^{\underline{N_m}} · 2^{6n+6} H(2ε)`. -/
private lemma val_Rser (n : ℕ) (h : Fin 6 → ℤ) (hadm : Admissible n h) (x : ℕ) :
    Rser n h ((x : ℚ) + 1 / 2) =
      (C (((2 * x + 1 + n : ℕ) : ℚ)) + C 2 * X) *
        ((∏ m : Fin 6, runPS (x + ((n : ℤ) + h m).toNat) (((n : ℤ) + 2 * h m).toNat)) *
          (C ((2 : ℚ) ^ (6 * n + 6)) * rescale 2 (H6 n x))) := by
  unfold Rser numSer
  rw [val_den, Finset.prod_congr rfl (fun m _ => offsets_prod n x (h m) (hadm.len_nonneg m))]
  have e1 : (2 : ℚ) * ((x : ℚ) + 1 / 2) + n = ((2 * x + 1 + n : ℕ) : ℚ) := by
    push_cast
    ring
  rw [e1]
  ring

/-! ### Legendre -/

/-- `v₂(N!) = N - s₂(N) ≥ N - ⌊log₂ N⌋ - 1`. -/
private lemma val_legendre (N L : ℕ) (hNL : Nat.log 2 N ≤ L) :
    (N : ℤ) - (L + 1) ≤ (padicValNat 2 N.factorial : ℤ) := by
  have h1 := sub_one_mul_padicValNat_factorial (p := 2) N
  have h3 := Nat.digit_sum_le 2 N
  have h2 : (Nat.digits 2 N).sum ≤ Nat.log 2 N + 1 := by
    rcases Nat.eq_zero_or_pos N with h0 | hN
    · subst h0
      simp
    · calc (Nat.digits 2 N).sum ≤ (Nat.digits 2 N).length • 1 :=
            List.sum_le_length_nsmul _ _ (fun d hd => by
              have := Nat.digits_lt_base (by norm_num) hd
              omega)
        _ = Nat.log 2 N + 1 := by
            rw [smul_eq_mul, mul_one, Nat.length_digits 2 N (by norm_num) hN.ne']
  norm_num at h1
  omega

/-! ### The theorem -/

theorem Valuation_proof (hIT : Stmt_IntegrandTaylor) (hD : Stmt_Delta) (hDF : Stmt_DeltaFun) :
    Stmt_Valuation := by
  refine ⟨6 ^ 10, 10, fun n h hadm I hI => ?_⟩
  have hsum : h 0 + h 1 + h 2 + h 3 + h 4 + h 5 = 0 := by
    have := hadm.sum_eq
    rwa [Fin.sum_univ_six] at this
  have hl0 := hadm.len_nonneg 0
  have hl1 := hadm.len_nonneg 1
  have hl2 := hadm.len_nonneg 2
  have hl3 := hadm.len_nonneg 3
  have hl4 := hadm.len_nonneg 4
  have hl5 := hadm.len_nonneg 5
  set L : ℕ := Nat.log 2 (6 * n) with hL
  -- the run lengths `N_m = n + 2 h_m ≤ 6n`
  have hlen : ∀ m : Fin 6, ((n : ℤ) + 2 * h m).toNat ≤ 6 * n := by
    intro m
    fin_cases m <;> simp <;> omega
  have hlog : ∀ m : Fin 6, Nat.log 2 (((n : ℤ) + 2 * h m).toNat) ≤ L := fun m =>
    Nat.log_mono_right (hlen m)
  -- `SerGood` for the product form
  have hQ : SerGood L (∑ m : Fin 6, (padicValNat 2 (((n : ℤ) + 2 * h m).toNat).factorial : ℤ))
      (fun x => ∏ m : Fin 6, runPS (x + ((n : ℤ) + h m).toNat) (((n : ℤ) + 2 * h m).toNat)) :=
    serGood_prod hD univ _ _ (fun m _ => serGood_run hD hDF _ _ L (hlog m))
  have hTot := serGood_mul hD (serGood_lin hD hDF n L) (serGood_mul hD hQ (serGood_H hD n L))
  set E : ℤ := 0 + ((∑ m : Fin 6, (padicValNat 2 (((n : ℤ) + 2 * h m).toNat).factorial : ℤ)) +
    ((6 * n + 6 : ℕ) : ℤ)) with hE
  have h3 := hTot 3
  -- the integrand is `(-6 · 2^{E - 3L}) ·` (a `VGood L` function)
  have hf : (fun x => ((integrand n h x : ℚ) : ℚ_[2])) = fun x =>
      ((-6 : ℚ_[2]) * (2 : ℚ_[2]) ^ (E - 3 * L)) *
        ((2 : ℚ_[2]) ^ (((3 : ℕ) : ℤ) * L - E) *
          ((coeff 3 ((C (((2 * x + 1 + n : ℕ) : ℚ)) + C 2 * X) *
            ((∏ m : Fin 6, runPS (x + ((n : ℤ) + h m).toNat) (((n : ℤ) + 2 * h m).toNat)) *
              (C ((2 : ℚ) ^ (6 * n + 6)) * rescale 2 (H6 n x)))) : ℚ) : ℚ_[2])) := by
    funext x
    rw [hIT n h hadm x, val_Rser n h hadm x]
    have e0 : (E - 3 * L) + (((3 : ℕ) : ℤ) * L - E) = 0 := by
      push_cast
      ring
    have e1 : ∀ c : ℚ_[2], ((-6 : ℚ_[2]) * (2 : ℚ_[2]) ^ (E - 3 * L)) *
        ((2 : ℚ_[2]) ^ (((3 : ℕ) : ℤ) * L - E) * c) = -6 * c := by
      intro c
      rw [mul_assoc, ← mul_assoc ((2 : ℚ_[2]) ^ (E - 3 * L)), ← zpow_add₀ (two_ne_zero), e0,
        zpow_zero, one_mul]
    rw [e1]
    push_cast
    ring
  have h6 : ‖(-6 : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-(1 : ℤ)) := by
    rw [norm_neg, show (6 : ℚ_[2]) = 2 * ((3 : ℕ) : ℚ_[2]) by norm_num, norm_mul]
    have h2 : ‖(2 : ℚ_[2])‖ = (2 : ℝ) ^ (-(1 : ℤ)) := by
      have := val_norm_two_zpow 1
      simpa using this
    rw [h2]
    calc (2 : ℝ) ^ (-(1 : ℤ)) * ‖((3 : ℕ) : ℚ_[2])‖ ≤ (2 : ℝ) ^ (-(1 : ℤ)) * 1 := by
          gcongr
          exact val_norm_natCast_le_one 3
      _ = _ := mul_one _
  have hK : ‖(-6 : ℚ_[2]) * (2 : ℚ_[2]) ^ (E - 3 * L)‖ ≤ (2 : ℝ) ^ (-(E - 3 * L + 1)) := by
    rw [norm_mul, val_norm_two_zpow]
    calc ‖(-6 : ℚ_[2])‖ * (2 : ℝ) ^ (-(E - 3 * L)) ≤
        (2 : ℝ) ^ (-(1 : ℤ)) * (2 : ℝ) ^ (-(E - 3 * L)) := by gcongr
      _ = (2 : ℝ) ^ (-(E - 3 * L + 1)) := by
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
          congr 1
          ring
  have hΔ : DeltaAll (-(L : ℤ) + (E - 3 * L + 1)) (fun x => ((integrand n h x : ℚ) : ℚ_[2])) := by
    rw [hf]
    exact hD.smulAll _ _ _ _ hK h3.2
  -- every Riemann sum, hence the limit, has `‖·‖ ≤ 2^{4L - E}`
  have hIle : ‖I‖ ≤ (2 : ℝ) ^ (1 - (-(L : ℤ) + (E - 3 * L + 1))) :=
    le_of_tendsto' hI.norm (fun M => hD.riemannAll _ _ hΔ M)
  -- Legendre: `E ≥ 12 n - 6 L`
  have hleg : ∀ m : Fin 6, (((n : ℤ) + 2 * h m).toNat : ℤ) - (L + 1) ≤
      (padicValNat 2 (((n : ℤ) + 2 * h m).toNat).factorial : ℤ) := fun m =>
    val_legendre _ L (hlog m)
  have hEge : 12 * (n : ℤ) - 6 * L ≤ E := by
    have hs := Finset.sum_le_sum (fun m (_ : m ∈ (univ : Finset (Fin 6))) => hleg m)
    rw [Fin.sum_univ_six, Fin.sum_univ_six] at hs
    rw [hE, Fin.sum_univ_six]
    omega
  have hIle' : ‖I‖ ≤ (2 : ℝ) ^ ((10 * L : ℤ) - (12 * n : ℤ)) :=
    hIle.trans (zpow_le_zpow_right₀ (by norm_num) (by omega))
  -- final numerics: `2^{10L} ≤ (6(n+1))^{10}`
  have h2L : (2 : ℝ) ^ L ≤ 6 * ((n : ℝ) + 1) := by
    have : 2 ^ L ≤ 6 * n + 1 := by
      rcases Nat.eq_zero_or_pos (6 * n) with h0 | hpos
      · rw [hL, h0]
        simp
      · exact (Nat.pow_log_le_self 2 hpos.ne').trans (Nat.le_succ _)
    calc (2 : ℝ) ^ L = ((2 ^ L : ℕ) : ℝ) := by push_cast; ring
      _ ≤ ((6 * n + 1 : ℕ) : ℝ) := by exact_mod_cast this
      _ ≤ 6 * ((n : ℝ) + 1) := by push_cast; linarith
  have hpow :
      (2 : ℝ) ^ ((10 * L : ℤ) - (12 * n : ℤ)) * (2 : ℝ) ^ (12 * n) = ((2 : ℝ) ^ L) ^ 10 := by
    rw [← zpow_natCast (2 : ℝ) (12 * n), ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0), ← pow_mul,
      ← zpow_natCast]
    congr 1
    push_cast
    ring
  calc ‖I‖ * (2 : ℝ) ^ (12 * n) ≤ (2 : ℝ) ^ ((10 * L : ℤ) - (12 * n : ℤ)) * (2 : ℝ) ^ (12 * n) := by
        gcongr
    _ = ((2 : ℝ) ^ L) ^ 10 := hpow
    _ ≤ (6 * ((n : ℝ) + 1)) ^ 10 := by gcongr
    _ = 6 ^ 10 * ((n : ℝ) + 1) ^ 10 := by ring

end Zeta2.Pair

end
