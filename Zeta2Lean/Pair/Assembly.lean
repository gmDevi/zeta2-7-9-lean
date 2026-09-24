import Zeta2Lean.Pair.Statements

/-!
# Zeta2Lean.Pair.Assembly — the logical skeleton of the pair theorem (complete, no gaps)

`main_of_stmts` derives `PairStatement` (convergence of all `J s`; `ζ₂(7)`, `ζ₂(9)` not both
rational) for **any** configuration `cfg` and rates `g, δ` with `g + δ < 12 log 2`, from:
* `Stmt_JConv`, `Stmt_Criterion` (reused from the `{7,9,11}` project), `Stmt_L1`, `Stmt_Valuation`
  (routine lemmas of the pair blueprint), and
* the three open gaps `Stmt_Growth cfg g`, `Stmt_Denominators cfg δ`, `Stmt_Nonvanishing cfg`,
  and PNT (cited; only passed on to `Stmt_Denominators`).

Argument (proof.md §8 with the pair data): suppose `ζ₂(7) = q₇`, `ζ₂(9) = q₉` rational.
* `L_m := D_m S_{n_m} = a_{m,0} + a_{m,1} ζ₂(7) + a_{m,2} ζ₂(9)` with integers
  `a_m = D_m (ρ₀, Z₇, Z₉)` (eventually, `Stmt_Denominators`; the integers are taken as numerators of
  the rationals `D_m ρ₀` etc., so no choice is needed);
* `B_m := |a_{m,0}| + |a_{m,1}| + |a_{m,2}|` trivially bounds every coefficient;
* `L_m ≠ 0` frequently (`Stmt_Nonvanishing` under the rationality assumption, `Stmt_L1`);
* eventually `B_m ‖L_m‖₂ ≤ 3 exp((g+ε)n) · (D_m ‖D_m‖₂) · ‖S_n‖₂
  ≤ 3c (n+1)^A exp(-(12 log 2 - g - δ - 2ε) n) → 0` with `ε = (12 log 2 - g - δ)/4`
  (`Stmt_Growth`, `Stmt_Denominators`, `Stmt_Valuation`, `n = cfg.n m → ∞`);
* Lai's criterion (`Stmt_Criterion`) gives the contradiction.

`marginE : gE + deltaE < 12 log 2` checks the target constants of configuration E.
-/

set_option linter.style.longLine false

open Filter Topology Finset

noncomputable section

namespace Zeta2.Pair

/-- The `J`-form of `Stmt_L1` equals the `ζ₂`-form `ρ₀ + Z₇ ζ₂(7) + Z₉ ζ₂(9)`. -/
theorem linear_form_zeta (n : ℕ) (h : Fin 6 → ℤ) :
    (rho0 n h : ℚ_[2]) + 60 * (csum n h 3 : ℚ_[2]) * J 6 + 210 * (csum n h 5 : ℚ_[2]) * J 8 =
      Lform n h := by
  simp only [Lform, Z7, Z9, zeta2]
  push_cast
  norm_num
  ring

/-- Given `Stmt_L1`, the value `S_n` (defined by `limUnder`) is the linear form. -/
theorem Sn_eq_Lform (hL1 : Stmt_L1) {n : ℕ} {h : Fin 6 → ℤ} (hh : Admissible n h) :
    Sn n h = Lform n h := by
  have := hL1 n h hh
  rw [linear_form_zeta] at this
  exact this.volkenborn_eq

/-- The target constants of configuration E satisfy the margin condition:
`-0.72 + 9 = 8.28 < 12 log 2 = 8.3178`. -/
theorem marginE : gE + deltaE < 12 * Real.log 2 := by
  have := Real.log_two_gt_d9
  unfold gE deltaE
  norm_num at this ⊢
  linarith

/-- `(x+1)^A e^{-κx} → 0` for `κ > 0`. -/
theorem tendsto_poly_mul_exp_neg {κ : ℝ} (hκ : 0 < κ) (A : ℕ) :
    Tendsto (fun x : ℝ => (x + 1) ^ A * Real.exp (-(κ * x))) atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => κ * (x + 1)) atTop atTop :=
    Tendsto.const_mul_atTop hκ (tendsto_atTop_add_const_right _ 1 tendsto_id)
  have h2 := ((Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero A).comp h1).const_mul
    ((κ ^ A)⁻¹ * Real.exp κ)
  rw [mul_zero] at h2
  refine h2.congr' (Eventually.of_forall fun x => ?_)
  have hk : κ ^ A ≠ 0 := pow_ne_zero _ hκ.ne'
  have he : Real.exp (-(κ * (x + 1))) = Real.exp (-(κ * x)) * (Real.exp κ)⁻¹ := by
    rw [show -(κ * (x + 1)) = -(κ * x) + -κ by ring, Real.exp_add, Real.exp_neg κ]
  simp only [Function.comp_apply]
  rw [he, mul_pow]
  field_simp

/-- `2^{12n} = exp(12 n log 2)`. -/
theorem two_pow_eq_exp (n : ℕ) : (2 : ℝ) ^ (12 * n) = Real.exp (12 * (n : ℝ) * Real.log 2) := by
  rw [show 12 * (n : ℝ) * Real.log 2 = ((12 * n : ℕ) : ℝ) * Real.log 2 by push_cast; ring,
    Real.exp_nat_mul, Real.exp_log two_pos]

/-- The analytic core of the assembly: with the three bounds at one step,
`D (|ρ₀|+|Z₇|+|Z₉|) · (‖D‖₂ ‖S‖₂) ≤ 3c (n+1)^A exp(-(12 log 2 - g - δ - 2ε) n)`. -/
theorem bound_core {g δ ε c : ℝ} {A n D : ℕ} {ρ z7 z9 normD normI : ℝ}
    (hg : |ρ| ≤ Real.exp ((g + ε) * n) ∧ |z7| ≤ Real.exp ((g + ε) * n) ∧
      |z9| ≤ Real.exp ((g + ε) * n))
    (hd : (D : ℝ) * normD ≤ Real.exp ((δ + ε) * n))
    (hv : normI * (2 : ℝ) ^ (12 * n) ≤ c * ((n : ℝ) + 1) ^ A)
    (hnD : 0 ≤ normD) (hnI : 0 ≤ normI) :
    (D : ℝ) * (|ρ| + |z7| + |z9|) * (normD * normI) ≤
      3 * c * ((n : ℝ) + 1) ^ A * Real.exp (-((12 * Real.log 2 - g - δ - 2 * ε) * n)) := by
  obtain ⟨g0, g1, g2⟩ := hg
  have hP : 0 < (2 : ℝ) ^ (12 * n) := by positivity
  have hX : |ρ| + |z7| + |z9| ≤ 3 * Real.exp ((g + ε) * n) := by linarith
  have hY0 : 0 ≤ (D : ℝ) * normD := mul_nonneg (Nat.cast_nonneg _) hnD
  have hZ0 : 0 ≤ normI * (2 : ℝ) ^ (12 * n) := mul_nonneg hnI hP.le
  have hE0 : 0 ≤ 3 * Real.exp ((g + ε) * n) := by positivity
  have hXY : (|ρ| + |z7| + |z9|) * ((D : ℝ) * normD) ≤
      3 * Real.exp ((g + ε) * n) * Real.exp ((δ + ε) * n) :=
    mul_le_mul hX hd hY0 hE0
  have hXYZ : (|ρ| + |z7| + |z9|) * ((D : ℝ) * normD) * (normI * (2 : ℝ) ^ (12 * n)) ≤
      3 * Real.exp ((g + ε) * n) * Real.exp ((δ + ε) * n) * (c * ((n : ℝ) + 1) ^ A) :=
    mul_le_mul hXY hv hZ0 (by positivity)
  have hE : Real.exp ((g + ε) * n) * Real.exp ((δ + ε) * n) =
      Real.exp (-((12 * Real.log 2 - g - δ - 2 * ε) * n)) * (2 : ℝ) ^ (12 * n) := by
    rw [two_pow_eq_exp, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  rw [← mul_le_mul_iff_of_pos_right hP]
  calc (D : ℝ) * (|ρ| + |z7| + |z9|) * (normD * normI) * (2 : ℝ) ^ (12 * n)
      = (|ρ| + |z7| + |z9|) * ((D : ℝ) * normD) * (normI * (2 : ℝ) ^ (12 * n)) := by ring
    _ ≤ 3 * Real.exp ((g + ε) * n) * Real.exp ((δ + ε) * n) * (c * ((n : ℝ) + 1) ^ A) := hXYZ
    _ = 3 * c * ((n : ℝ) + 1) ^ A * (Real.exp ((g + ε) * n) * Real.exp ((δ + ε) * n)) := by ring
    _ = 3 * c * ((n : ℝ) + 1) ^ A * Real.exp (-((12 * Real.log 2 - g - δ - 2 * ε) * n)) *
          (2 : ℝ) ^ (12 * n) := by rw [hE]; ring

/-- Cast of the numerator of a rational that is an integer. -/
theorem num_cast_of_eq_int {x : ℚ} {z : ℤ} (h : x = z) :
    ((x.num : ℤ) : ℚ_[2]) = ((x : ℚ) : ℚ_[2]) := by
  rw [h, Rat.num_intCast]
  simp

/-- Absolute value of the numerator of a rational that is an integer. -/
theorem num_abs_of_eq_int {x : ℚ} {z : ℤ} (h : x = z) :
    |((x.num : ℤ) : ℝ)| = |((x : ℚ) : ℝ)| := by
  rw [h, Rat.num_intCast]
  simp

/-- **Assembly (proof.md §8 for the pair).**  Any configuration, any rates with
`g + δ < 12 log 2`. -/
theorem main_of_stmts (cfg : Config) (g δ : ℝ) (hmargin : g + δ < 12 * Real.log 2)
    (hJ : Stmt_JConv) (hL1 : Stmt_L1) (hVal : Stmt_Valuation) (hCrit : Stmt_Criterion)
    (hG : Stmt_Growth cfg g) (hD : Stmt_Denominators cfg δ) (hNV : Stmt_Nonvanishing cfg)
    (hPNT : PNT_Stmt) : PairStatement := by
  refine ⟨hJ, ?_⟩
  rintro ⟨h7, h9⟩
  obtain ⟨D, hDint, hDbd⟩ := hD hPNT
  obtain ⟨c, A, hv⟩ := hVal
  have hNVf := hNV h7 h9
  -- the value of the linear form
  have hI : ∀ m, HasVolkenborn (fun x => ((integrand (cfg.n m) (cfg.h m) x : ℚ) : ℚ_[2]))
      (Lform (cfg.n m) (cfg.h m)) := by
    intro m
    have := hL1 (cfg.n m) (cfg.h m) (cfg.adm m)
    rwa [linear_form_zeta] at this
  -- the sequences of the criterion
  let α : Fin 2 → ℚ_[2] := ![zeta2 7, zeta2 9]
  let a₀ : ℕ → ℤ := fun m => ((D m : ℚ) * rho0 (cfg.n m) (cfg.h m)).num
  let a' : ℕ → Fin 2 → ℤ := fun m =>
    ![((D m : ℚ) * Z7 (cfg.n m) (cfg.h m)).num, ((D m : ℚ) * Z9 (cfg.n m) (cfg.h m)).num]
  let B : ℕ → ℝ := fun m => |(a₀ m : ℝ)| + |(a' m 0 : ℝ)| + |(a' m 1 : ℝ)|
  have hform : ∀ m, ClearsDen (D m) (cfg.n m) (cfg.h m) →
      (a₀ m : ℚ_[2]) + ∑ j, (a' m j : ℚ_[2]) * α j =
        (D m : ℚ_[2]) * Lform (cfg.n m) (cfg.h m) := by
    rintro m ⟨-, ⟨z0, hz0⟩, ⟨z1, hz1⟩, ⟨z2, hz2⟩⟩
    simp only [a₀, a', α, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Lform]
    rw [num_cast_of_eq_int hz0, num_cast_of_eq_int hz1, num_cast_of_eq_int hz2]
    push_cast
    ring
  have hB : ∀ m, ClearsDen (D m) (cfg.n m) (cfg.h m) →
      B m = (D m : ℝ) * (|(rho0 (cfg.n m) (cfg.h m) : ℝ)| + |(Z7 (cfg.n m) (cfg.h m) : ℝ)| +
        |(Z9 (cfg.n m) (cfg.h m) : ℝ)|) := by
    rintro m ⟨-, ⟨z0, hz0⟩, ⟨z1, hz1⟩, ⟨z2, hz2⟩⟩
    simp only [B, a₀, a', Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [num_abs_of_eq_int hz0, num_abs_of_eq_int hz1, num_abs_of_eq_int hz2]
    push_cast
    rw [abs_mul, abs_mul, abs_mul, Nat.abs_cast]
    ring
  have hB0 : ∀ m, 0 ≤ B m := fun m => by simp only [B]; positivity
  apply hCrit 2 α a₀ a' B
  · -- `|a_{m,0}| ≤ B m`
    intro m
    have := abs_nonneg (a' m 0 : ℝ)
    have := abs_nonneg (a' m 1 : ℝ)
    simp only [B]
    linarith
  · -- `|a_{m,j}| ≤ B m`
    intro m j
    have := abs_nonneg (a₀ m : ℝ)
    have := abs_nonneg (a' m 0 : ℝ)
    have := abs_nonneg (a' m 1 : ℝ)
    fin_cases j
    · simp only [B, Fin.zero_eta]
      linarith
    · simp only [B, Fin.mk_one]
      linarith
  · -- the linear forms are frequently non-zero
    refine (hNVf.and_eventually hDint).mono fun m hm => ?_
    obtain ⟨hne, hcl⟩ := hm
    rw [hform m hcl]
    exact mul_ne_zero (by exact_mod_cast hcl.1.ne') (hne _ (hI m))
  · -- `B m · ‖L_m‖ → 0`
    set ε : ℝ := (12 * Real.log 2 - g - δ) / 4 with hε
    have hε0 : 0 < ε := by rw [hε]; linarith
    have hκ : 0 < 12 * Real.log 2 - g - δ - 2 * ε := by rw [hε]; linarith
    have hlim : Tendsto (fun m => 3 * c * (((cfg.n m : ℕ) : ℝ) + 1) ^ A *
        Real.exp (-((12 * Real.log 2 - g - δ - 2 * ε) * (cfg.n m : ℝ)))) atTop (𝓝 0) := by
      have h1 := ((tendsto_poly_mul_exp_neg hκ A).comp
        (tendsto_natCast_atTop_atTop.comp cfg.tendsto)).const_mul (3 * c)
      rw [mul_zero] at h1
      refine h1.congr' (Eventually.of_forall fun m => ?_)
      simp only [Function.comp_apply]
      ring
    refine squeeze_zero' (Eventually.of_forall fun m => mul_nonneg (hB0 m) (norm_nonneg _)) ?_ hlim
    filter_upwards [hDint, hG ε hε0, hDbd ε hε0] with m hcl hgr hdb
    rw [hform m hcl, norm_mul, hB m hcl]
    exact bound_core hgr hdb (hv _ _ (cfg.adm m) _ (hI m)) (norm_nonneg _) (norm_nonneg _)
  · -- both values rational
    intro j
    fin_cases j
    · exact h7
    · exact h9

end Zeta2.Pair

end
