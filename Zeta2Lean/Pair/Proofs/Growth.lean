import Zeta2Lean.Pair.Statements

/-!
# GAP 1 (growth): exponential decay of `ρ₀, Z₇, Z₉` for configuration E

gap: 'growth'.  **Task.** `Stmt_Growth configE gE`: for every `ε > 0`, eventually in `m`
(`n = 40 m`, `h = m · (-17, 1, 2, 3, 5, 6)`), `|ρ₀|, |Z₇|, |Z₉| ≤ exp((-0.72 + ε) n)`.

## Proof as formalized (track `pair79/growth`, contour integrals with half-integer kernels)

Everything is proved except two explicit numerical inequalities for the landscape function (the
"computer-assisted" part of the informal proof), isolated as `GrowthAux.landscape_real` and
`GrowthAux.landscape_vert` (see the end of this docstring).

1. **Kernels** (`kerS s t = ∑_{ν ∈ ℤ} (t - ν - 1/2)^{-s}`, `s ≥ 2`): holomorphic off the
   half-integers, bounded on vertical lines through integers, and `O(e^{-2π Im t})` for
   `Im t ≥ 1` (`kerS_decay`, via the Eisenstein `q`-expansion identity).
   (They replace `(π sec πt)²`, `(π sec πt)⁴`, `(π tan πt)''''` of the informal proof.)
2. **Vertical-line representation** (`vline_Pc_kerS`): for the line `Re t = m = n/40`,
   `∫ R_n(m+iy) K_s(m+iy) dy = -2π ∑_{l ≥ 0} D_{s-1}(m + l + 1/2)` (`D_j` = `j`-th Taylor
   coefficient of `R_n`), by Cauchy's formula on right half-planes (`vline_higher`,
   `vline_left`, derived from `Complex.integral_boundary_rect_eq_zero_of_differentiableOn`) and
   dominated interchange of `∑_ν` and `∫`.  With the critical zeros (`Dc_hpt_eq_zero`: `R_n`
   vanishes to order `≥ 5` at the half-integers in `(-n - n/40, n/40)`), the symmetry
   `R_n(-n-t) = -R_n(t)` and `c₁ = c₂ = c₄ = c₆ = 0` this gives (`Iker_two/four/five`)
   `I₂ = π (3 c₃ Z₄ + 5 c₅ Z₆)`, `I₄ = π (10 c₃ Z₆ + 35 c₅ Z₈)`,
   `I₅ = -2π (15 c₃ Z⁺₇ + 70 c₅ Z⁺₉ + ρ₀/24)` (`Z_s = ∑_{ν∈ℤ} (ν+1/2)^{-s}`,
   `Z⁺_s = ∑_{l≥0} (l+1/2)^{-s}`).  The determinant `105 Z₄ Z₈ - 50 Z₆²` is `> 0` by
   Cauchy–Schwarz (`det_pos`), hence `|ρ₀|, |Z₇|, |Z₉| ≤ K (|I₂| + |I₄| + |I₅|)`
   (`coeff_le_Iker`).
3. **Contour** (`Iker_le`): by conjugation symmetry only the upper half-line matters; it is cut at
   height `1`, and the part above height `1` is shifted from `Re t = m` to `Re t = 0.07 n`
   (`halfstrip_shift`).  Pieces: A (`m + iy`, `0 ≤ y ≤ 1`: comparison with `m + i`,
   `norm_Rc_vert_le`), B (`x + i`, `m ≤ x ≤ 0.07 n`), C₁ (`0.07 n + iy`, `1 ≤ y ≤ n`),
   C₂ (`y ≥ n`).
4. **Pointwise bound** (`norm_Rc_le`, window comparison of `∑ log|t + j|` with integrals):
   `|R_n(t)| ≤ |2t + n| (|t| + 2n)^6 exp(n Φ(t/n))` for `Re t ≥ 0`, `Im t ≥ 1`, where
   `Φ(x, y) = PhiE x y = ∑_p [G(x+1+η_p, y) - G(x-η_p, y)] - 6 [G(x+1, y) - G(x, y)]`,
   `G(a, y) = (a/2) log(a² + y²) + y arctan(a/y) - a` (`Gf`), i.e. `Φ = Re φ` of the informal
   proof.  Analytic landscape facts (proved): `Φ(ξ, η) ≤ Φ(ξ, 0) + 6πη` (`PhiE_le_add`,
   `∂_η Φ ≤ 6π`) and `Φ(ξ, η) ≤ 4` for `η ≥ 1` (`PhiE_le_four`, second-order Taylor).
5. **Result**: `|I_s| ≤ C m⁸ e^{-0.72 · 40 m}` (`Iker_le`), hence the statement
   (`growth_main`).  (The informal proof's sharp rate `-0.78127` is not needed: the contour only
   has to stay below the target `gE = -0.72`.)

## What remains (`sorry`): two concrete numerical inequalities

* `landscape_real : ∀ ξ ∈ [1/40, 7/100], PhiE ξ 0 ≤ -18/25` — the real profile
  `P(ξ) = ∑_j s_j (ξ + a_j) log|ξ + a_j|` (only logarithms); true maximum `-0.80049` (at
  `ξ ≈ 0.02503`), margin `0.08`.
* `landscape_vert : ∀ η ∈ (0, 1], PhiE (7/100) η - 2πη ≤ -18/25` — the vertical line through
  the saddle point `τ* = 0.06959 + 0.03128 i` (logarithms and arctangents); true maximum
  `-0.78127` (at `η ≈ 0.031`), margin `0.061`.

Both are the standard/sharp parts of Lemma 7 of `pair79/growth/proof.md`, certified there by
interval arithmetic (`certify.py`, `vcertify.py`, `cert3.py`); they are checked numerically
(mpmath, 30 digits, grids of 45000 resp. 20000 points) in the prover's scratchpad
(`growthprover/check_land.py`).
-/

set_option linter.style.longLine false

open Complex MeasureTheory Filter Topology Set Finset PowerSeries
open scoped Real

noncomputable section

namespace Zeta2.Pair

namespace GrowthAux

-- (part: growth_base)

/-! ## Vertical-line integrals -/

/-- A continuous function on `ℝ` bounded by `C/(1+y²)` is integrable. -/
theorem integrable_of_bound_inv_one_add_sq {g : ℝ → ℂ} (hg : Continuous g) {C : ℝ}
    (hC : ∀ y, ‖g y‖ ≤ C * (1 + y ^ 2)⁻¹) : Integrable g :=
  (integrable_inv_one_add_sq.const_mul C).mono' hg.aestronglyMeasurable (Eventually.of_forall hC)

/-- If `g` is continuous and `‖g y‖ ≤ C / y²` for `|y| ≥ r ≥ 1`, then `‖g y‖ ≤ K (1+y²)⁻¹`. -/
theorem exists_bound_inv_one_add_sq {g : ℝ → ℂ} (hg : Continuous g) {C r : ℝ} (hr : 1 ≤ r)
    (hC0 : 0 ≤ C) (hC : ∀ y, r ≤ |y| → ‖g y‖ ≤ C / y ^ 2) :
    ∃ K, ∀ y, ‖g y‖ ≤ K * (1 + y ^ 2)⁻¹ := by
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := -r) (b := r)).exists_bound_of_continuousOn
    hg.continuousOn
  refine ⟨max (M * (1 + r ^ 2)) (2 * C), fun y => ?_⟩
  have hpos : 0 < 1 + y ^ 2 := by positivity
  by_cases hy : r ≤ |y|
  · have h1 := hC y hy
    have hy1 : 1 ≤ y ^ 2 := by
      have : 1 ≤ |y| := le_trans hr hy
      nlinarith [sq_abs y, abs_nonneg y]
    have hy2 : 0 < y ^ 2 := by linarith
    calc ‖g y‖ ≤ C / y ^ 2 := h1
      _ ≤ 2 * C * (1 + y ^ 2)⁻¹ := by
          rw [← div_eq_mul_inv, div_le_div_iff₀ hy2 hpos]
          nlinarith
      _ ≤ max (M * (1 + r ^ 2)) (2 * C) * (1 + y ^ 2)⁻¹ := by
          gcongr
          exact le_max_right _ _
  · push Not at hy
    have hy' : y ∈ Icc (-r) r := ⟨by linarith [neg_abs_le y], by linarith [le_abs_self y]⟩
    have h1 := hM y hy'
    have hM0 : 0 ≤ M := le_trans (norm_nonneg _) h1
    have hyr : y ^ 2 ≤ r ^ 2 := by
      have : |y| ≤ r := hy.le
      nlinarith [sq_abs y, abs_nonneg y]
    calc ‖g y‖ ≤ M := h1
      _ ≤ M * (1 + r ^ 2) * (1 + y ^ 2)⁻¹ := by
          rw [mul_assoc, ← div_eq_mul_inv]
          have : 1 ≤ (1 + r ^ 2) / (1 + y ^ 2) := by
            rw [le_div_iff₀ hpos]; linarith
          nlinarith
      _ ≤ max (M * (1 + r ^ 2)) (2 * C) * (1 + y ^ 2)⁻¹ := by
          gcongr
          exact le_max_left _ _

/-- The vertical line `y ↦ c + y i` is continuous. -/
theorem continuous_vline (c : ℝ) : Continuous fun y : ℝ => (c : ℂ) + (y : ℂ) * I := by
  fun_prop

theorem vline_re (c y : ℝ) : ((c : ℂ) + (y : ℂ) * I).re = c := by simp

theorem vline_im (c y : ℝ) : ((c : ℂ) + (y : ℂ) * I).im = y := by simp

theorem abs_le_norm_vline (c y : ℝ) : |y| ≤ ‖(c : ℂ) + (y : ℂ) * I‖ := by
  have := Complex.abs_im_le_norm ((c : ℂ) + (y : ℂ) * I)
  simpa using this

theorem abs_le_norm_vline_re (c y : ℝ) : |c| ≤ ‖(c : ℂ) + (y : ℂ) * I‖ := by
  have := Complex.abs_re_le_norm ((c : ℂ) + (y : ℂ) * I)
  simpa using this

/-- **Cauchy's theorem for a right half-plane.**  If `f` is holomorphic on `{Re t > c'}`, `c' < c`,
and `‖f t‖ ≤ C/‖t‖²` for `Re t ≥ c`, `‖t‖ ≥ r`, then `∫_ℝ f(c + y i) dy = 0` (and the integrand
is integrable). -/
theorem vline_integral_eq_zero {f : ℂ → ℂ} {c c' : ℝ} (hcc : c' < c)
    (hf : DifferentiableOn ℂ f {t | c' < t.re}) {C r : ℝ} (hr : 1 ≤ r) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℂ, c ≤ t.re → r ≤ ‖t‖ → ‖f t‖ ≤ C / ‖t‖ ^ 2) :
    Integrable (fun y : ℝ => f (c + y * I)) ∧ ∫ y : ℝ, f (c + y * I) = 0 := by
  have hopen : IsOpen {t : ℂ | c' < t.re} := isOpen_lt continuous_const Complex.continuous_re
  have hcont : Continuous fun y : ℝ => f (c + y * I) := by
    refine hf.continuousOn.comp_continuous (continuous_vline c) fun y => ?_
    show c' < ((c : ℂ) + (y : ℂ) * I).re
    rw [vline_re]; exact hcc
  -- decay along the line
  have hdec : ∀ y : ℝ, r ≤ |y| → ‖f (c + y * I)‖ ≤ C / y ^ 2 := by
    intro y hy
    have hn := abs_le_norm_vline c y
    have h1 := hC _ (by rw [vline_re]) (le_trans hy hn)
    have hy0 : 0 < |y| := lt_of_lt_of_le (by linarith) hy
    calc ‖f (c + y * I)‖ ≤ C / ‖(c : ℂ) + (y : ℂ) * I‖ ^ 2 := h1
      _ ≤ C / y ^ 2 := by
          rw [← sq_abs y]
          apply div_le_div_of_nonneg_left hC0 (pow_pos hy0 2)
          exact pow_le_pow_left₀ (abs_nonneg _) hn 2
  obtain ⟨K, hK⟩ := exists_bound_inv_one_add_sq hcont hr hC0 hdec
  have hint : Integrable (fun y : ℝ => f (c + y * I)) :=
    integrable_of_bound_inv_one_add_sq hcont hK
  refine ⟨hint, ?_⟩
  -- rectangle estimate
  have hrect : ∀ R : ℝ, r + |c| + 1 ≤ R →
      ‖∫ y in (-R)..R, f (c + y * I)‖ ≤ C * (4 + 2 * |c|) / R := by
    intro R hR
    have hR1 : 1 ≤ R := by linarith [abs_nonneg c]
    have hRpos : 0 < R := by linarith
    have hcR : c ≤ R := by linarith [le_abs_self c]
    have hrR : r ≤ R := by linarith [abs_nonneg c]
    set z : ℂ := ⟨c, -R⟩
    set w : ℂ := ⟨R, R⟩
    have hsub : Set.uIcc z.re w.re ×ℂ Set.uIcc z.im w.im ⊆ {t : ℂ | c' < t.re} := by
      intro t ht
      rw [Complex.mem_reProdIm] at ht
      have h1 := ht.1
      simp only [z, w] at h1
      rw [Set.uIcc_of_le hcR] at h1
      show c' < t.re
      linarith [h1.1]
    have key := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f z w (hf.mono hsub)
    simp only [z, w] at key
    -- bounds on the three other sides
    have hbot : ‖∫ x in c..R, f (↑x + ↑(-R) * I)‖ ≤ C / R ^ 2 * |R - c| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le hcR] at hx
      have hre : c ≤ ((x : ℂ) + ((-R : ℝ) : ℂ) * I).re := by simp; exact hx.1.le
      have hn : R ≤ ‖(x : ℂ) + ((-R : ℝ) : ℂ) * I‖ := by
        have := abs_le_norm_vline x (-R)
        rwa [abs_neg, abs_of_pos hRpos] at this
      calc ‖f (↑x + ↑(-R) * I)‖ ≤ C / ‖(x : ℂ) + ((-R : ℝ) : ℂ) * I‖ ^ 2 :=
            hC _ hre (le_trans hrR hn)
        _ ≤ C / R ^ 2 := by
            apply div_le_div_of_nonneg_left hC0 (by positivity)
            exact pow_le_pow_left₀ hRpos.le hn 2
    have htop : ‖∫ x in c..R, f (↑x + ↑R * I)‖ ≤ C / R ^ 2 * |R - c| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Set.uIoc_of_le hcR] at hx
      have hre : c ≤ ((x : ℂ) + (R : ℂ) * I).re := by simp; exact hx.1.le
      have hn : R ≤ ‖(x : ℂ) + (R : ℂ) * I‖ := by
        have := abs_le_norm_vline x R
        rwa [abs_of_pos hRpos] at this
      calc ‖f (↑x + ↑R * I)‖ ≤ C / ‖(x : ℂ) + (R : ℂ) * I‖ ^ 2 := hC _ hre (le_trans hrR hn)
        _ ≤ C / R ^ 2 := by
            apply div_le_div_of_nonneg_left hC0 (by positivity)
            exact pow_le_pow_left₀ hRpos.le hn 2
    have hright : ‖∫ y in (-R)..R, f (↑R + ↑y * I)‖ ≤ C / R ^ 2 * |R - (-R)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro y _
      have hre : c ≤ ((R : ℂ) + (y : ℂ) * I).re := by simp; exact hcR
      have hn : R ≤ ‖(R : ℂ) + (y : ℂ) * I‖ := by
        have := abs_le_norm_vline_re R y
        rwa [abs_of_pos hRpos] at this
      calc ‖f (↑R + ↑y * I)‖ ≤ C / ‖(R : ℂ) + (y : ℂ) * I‖ ^ 2 := hC _ hre (le_trans hrR hn)
        _ ≤ C / R ^ 2 := by
            apply div_le_div_of_nonneg_left hC0 (by positivity)
            exact pow_le_pow_left₀ hRpos.le hn 2
    have heq : I • ∫ y in (-R)..R, f (↑c + ↑y * I) =
        ((∫ x in c..R, f (↑x + ↑(-R) * I)) - ∫ x in c..R, f (↑x + ↑R * I)) +
          I • ∫ y in (-R)..R, f (↑R + ↑y * I) := by
      exact (sub_eq_zero.mp key).symm
    have hnorm : ‖∫ y in (-R)..R, f (↑c + ↑y * I)‖ =
        ‖I • ∫ y in (-R)..R, f (↑c + ↑y * I)‖ := by
      rw [norm_smul, Complex.norm_I, one_mul]
    rw [hnorm, heq]
    have habs1 : |R - c| ≤ R + |c| := by
      rw [abs_le]; constructor <;> linarith [le_abs_self c, neg_abs_le c]
    have habs2 : |R - (-R)| = 2 * R := by rw [sub_neg_eq_add, ← two_mul, abs_of_pos (by linarith)]
    calc ‖((∫ x in c..R, f (↑x + ↑(-R) * I)) - ∫ x in c..R, f (↑x + ↑R * I)) +
          I • ∫ y in (-R)..R, f (↑R + ↑y * I)‖
        ≤ ‖∫ x in c..R, f (↑x + ↑(-R) * I)‖ + ‖∫ x in c..R, f (↑x + ↑R * I)‖ +
            ‖∫ y in (-R)..R, f (↑R + ↑y * I)‖ := by
          refine le_trans (norm_add_le _ _) ?_
          rw [norm_smul, Complex.norm_I, one_mul]
          gcongr
          exact norm_sub_le _ _
      _ ≤ C / R ^ 2 * |R - c| + C / R ^ 2 * |R - c| + C / R ^ 2 * |R - (-R)| := by
          gcongr
      _ ≤ C / R ^ 2 * (R + |c|) + C / R ^ 2 * (R + |c|) + C / R ^ 2 * (2 * R) := by
          rw [habs2]
          have : 0 ≤ C / R ^ 2 := by positivity
          gcongr
      _ = C * (4 * R + 2 * |c|) / R ^ 2 := by ring
      _ ≤ C * (4 + 2 * |c|) / R := by
          rw [div_le_div_iff₀ (by positivity) hRpos]
          have : 0 ≤ C * |c| * R * (R - 1) :=
            mul_nonneg (mul_nonneg (mul_nonneg hC0 (abs_nonneg c)) hRpos.le) (by linarith)
          nlinarith [this]
  -- pass to the limit
  have hlim : Tendsto (fun R : ℝ => ∫ y in (-R)..R, f (c + y * I)) atTop
      (𝓝 (∫ y : ℝ, f (c + y * I))) :=
    intervalIntegral_tendsto_integral hint tendsto_neg_atTop_atBot tendsto_id
  have hlim0 : Tendsto (fun R : ℝ => ∫ y in (-R)..R, f (c + y * I)) atTop (𝓝 0) := by
    have hb : Tendsto (fun R : ℝ => C * (4 + 2 * |c|) / R) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop tendsto_id
    refine squeeze_zero_norm' ?_ hb
    filter_upwards [eventually_ge_atTop (r + |c| + 1)] with R hR
    exact hrect R hR
  exact tendsto_nhds_unique hlim hlim0

/-- The explicit kernel integral: `∫_ℝ ((c+iy-(c+p))⁻¹ - (c+iy-(c-p))⁻¹) dy = -2π` for `p > 0`. -/
theorem vline_integral_inv_sub {c p : ℝ} (hp : 0 < p) :
    Integrable (fun y : ℝ => ((c : ℂ) + y * I - ((c + p : ℝ) : ℂ))⁻¹ -
      ((c : ℂ) + y * I - ((c - p : ℝ) : ℂ))⁻¹) ∧
    ∫ y : ℝ, (((c : ℂ) + y * I - ((c + p : ℝ) : ℂ))⁻¹ -
      ((c : ℂ) + y * I - ((c - p : ℝ) : ℂ))⁻¹) = -2 * π := by
  have hpt : ∀ y : ℝ, ((c : ℂ) + y * I - ((c + p : ℝ) : ℂ))⁻¹ -
      ((c : ℂ) + y * I - ((c - p : ℝ) : ℂ))⁻¹ =
        (((-2 / p) * (1 + (p⁻¹ * y) ^ 2)⁻¹ : ℝ) : ℂ) := by
    intro y
    have h1 : (c : ℂ) + y * I - ((c + p : ℝ) : ℂ) = ((-p : ℝ) : ℂ) + (y : ℂ) * I := by
      push_cast; ring
    have h2 : (c : ℂ) + y * I - ((c - p : ℝ) : ℂ) = ((p : ℝ) : ℂ) + (y : ℂ) * I := by
      push_cast; ring
    rw [h1, h2]
    have hne1 : ((-p : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hne2 : ((p : ℝ) : ℂ) + (y : ℂ) * I ≠ 0 := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hreal : (-2 / p) * (1 + (p⁻¹ * y) ^ 2)⁻¹ = -(2 * p) / (p ^ 2 + y ^ 2) := by
      field_simp
    rw [hreal]
    have hprod : (((-p : ℝ) : ℂ) + (y : ℂ) * I) * (((p : ℝ) : ℂ) + (y : ℂ) * I) =
        -(((p ^ 2 + y ^ 2 : ℝ)) : ℂ) := by
      push_cast
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [inv_sub_inv hne1 hne2, hprod]
    have hpy : ((p ^ 2 + y ^ 2 : ℝ) : ℂ) ≠ 0 := by
      have : (0 : ℝ) < p ^ 2 + y ^ 2 := by positivity
      exact_mod_cast this.ne'
    push_cast
    field_simp
    ring
  have hint : Integrable (fun y : ℝ => ((c : ℂ) + y * I - ((c + p : ℝ) : ℂ))⁻¹ -
      ((c : ℂ) + y * I - ((c - p : ℝ) : ℂ))⁻¹) := by
    simp_rw [hpt]
    exact ((integrable_inv_one_add_mul_sq (inv_ne_zero hp.ne')).const_mul (-2 / p)).ofReal
  refine ⟨hint, ?_⟩
  simp_rw [hpt]
  rw [integral_complex_ofReal, integral_const_mul, integral_univ_inv_one_add_mul_sq]
  rw [abs_inv, abs_of_pos hp]
  have hp0 : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  push_cast
  field_simp

/-- **Cauchy's integral formula for a right half-plane** (simple pole):
`∫_ℝ F(c+iy) (c+iy-x)⁻¹ dy = -2π F(x)` for `x > c`, if `F` is holomorphic on `Re t > c'`
(`c' < c`) and `O(1/|t|)` there. -/
theorem vline_cauchy {F : ℂ → ℂ} {c c' : ℝ} (hcc : c' < c)
    (hF : DifferentiableOn ℂ F {t | c' < t.re}) {C r : ℝ} (hr : 1 ≤ r) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℂ, c ≤ t.re → r ≤ ‖t‖ → ‖F t‖ ≤ C / ‖t‖) {x : ℝ} (hx : c < x) :
    ∫ y : ℝ, F (c + y * I) * ((c : ℂ) + y * I - x)⁻¹ = -2 * π * F x := by
  set p : ℝ := x - c with hp_def
  have hp : 0 < p := by rw [hp_def]; linarith
  set a : ℝ := c - p with ha_def
  have hxcp : x = c + p := by rw [hp_def]; ring
  set c'' : ℝ := max c' a with hc''
  have hc''c : c'' < c := max_lt hcc (by rw [ha_def]; linarith)
  set U : Set ℂ := {t | c'' < t.re} with hU
  have hUopen : IsOpen U := isOpen_lt continuous_const Complex.continuous_re
  have hUsub : U ⊆ {t | c' < t.re} := by
    intro t ht
    show c' < t.re
    exact lt_of_le_of_lt (le_max_left _ _) ht
  have hxU : (x : ℂ) ∈ U := by
    show c'' < ((x : ℂ)).re
    simp only [Complex.ofReal_re]; linarith
  set H : ℂ → ℂ := fun t => dslope F x t + F x * (t - a)⁻¹ with hH
  have hHdiff : DifferentiableOn ℂ H U := by
    refine DifferentiableOn.add ?_ ?_
    · exact (Complex.differentiableOn_dslope (hUopen.mem_nhds hxU)).2 (hF.mono hUsub)
    · refine DifferentiableOn.mul (differentiableOn_const _) ?_
      refine DifferentiableOn.inv (differentiableOn_id.sub (differentiableOn_const _)) ?_
      intro t ht h
      have : t.re = a := by
        have := congrArg Complex.re h
        simpa [sub_eq_zero] using this
      have h2 : c'' < t.re := ht
      have : a ≤ c'' := le_max_right _ _
      linarith
  -- decay of `H`
  set r₁ : ℝ := max r (2 * |x| + 2 * |a| + 1) with hr₁
  have hr₁1 : 1 ≤ r₁ := le_trans hr (le_max_left _ _)
  have hHdec : ∀ t : ℂ, c ≤ t.re → r₁ ≤ ‖t‖ →
      ‖H t‖ ≤ (2 * C + 4 * ‖F x‖ * |a - x|) / ‖t‖ ^ 2 := by
    intro t htre htn
    have htr : r ≤ ‖t‖ := le_trans (le_max_left _ _) htn
    have ht2 : 2 * |x| + 2 * |a| + 1 ≤ ‖t‖ := le_trans (le_max_right _ _) htn
    have htpos : 0 < ‖t‖ := by linarith [abs_nonneg x, abs_nonneg a]
    have hx2 : ‖t‖ / 2 ≤ ‖t - x‖ := by
      have := norm_sub_norm_le t (x : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith [abs_nonneg a]
    have ha2 : ‖t‖ / 2 ≤ ‖t - a‖ := by
      have := norm_sub_norm_le t (a : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith [abs_nonneg x]
    have htx : t ≠ (x : ℂ) := by
      intro h; rw [h, Complex.norm_real, Real.norm_eq_abs] at ht2
      linarith [abs_nonneg a, abs_nonneg x]
    have hta : t - a ≠ 0 := by
      intro h; rw [h, norm_zero] at ha2; linarith
    have htx' : t - x ≠ 0 := sub_ne_zero.mpr htx
    have hHt : H t = F t * (t - x)⁻¹ + F x * (a - x) * ((t - a)⁻¹ * (t - x)⁻¹) := by
      simp only [hH]
      rw [dslope_of_ne _ htx, slope_def_field]
      field_simp
      ring
    rw [hHt]
    have hn1 : ‖F t * (t - x)⁻¹‖ ≤ C / ‖t‖ * (2 / ‖t‖) := by
      rw [norm_mul, norm_inv]
      gcongr
      · exact hC t htre htr
      · rw [inv_le_comm₀ (by positivity) (by positivity)]
        rw [inv_div]; exact hx2
    have hn2 : ‖F x * (a - x) * ((t - a)⁻¹ * (t - x)⁻¹)‖ ≤
        ‖F x‖ * |a - x| * ((2 / ‖t‖) * (2 / ‖t‖)) := by
      rw [norm_mul, norm_mul, norm_mul, norm_inv, norm_inv]
      have : ‖((a : ℂ) - x)‖ = |a - x| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
      rw [this]
      gcongr
      · rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]; exact ha2
      · rw [inv_le_comm₀ (by positivity) (by positivity), inv_div]; exact hx2
    calc ‖F t * (t - x)⁻¹ + F x * (a - x) * ((t - a)⁻¹ * (t - x)⁻¹)‖
        ≤ C / ‖t‖ * (2 / ‖t‖) + ‖F x‖ * |a - x| * ((2 / ‖t‖) * (2 / ‖t‖)) :=
          le_trans (norm_add_le _ _) (add_le_add hn1 hn2)
      _ = (2 * C + 4 * ‖F x‖ * |a - x|) / ‖t‖ ^ 2 := by
          field_simp
          ring
  obtain ⟨hHint, hHzero⟩ := vline_integral_eq_zero hc''c (hHdiff.mono fun t ht => ht) hr₁1
    (by positivity) hHdec
  obtain ⟨hKint, hKval⟩ := vline_integral_inv_sub (c := c) hp
  -- pointwise decomposition on the line
  have hdecomp : ∀ y : ℝ, F (c + y * I) * ((c : ℂ) + y * I - x)⁻¹ =
      H (c + y * I) + F x * (((c : ℂ) + y * I - ((c + p : ℝ) : ℂ))⁻¹ -
        ((c : ℂ) + y * I - ((c - p : ℝ) : ℂ))⁻¹) := by
    intro y
    have hne : (c : ℂ) + y * I ≠ (x : ℂ) := by
      intro h
      have := congrArg Complex.re h
      simp at this
      linarith
    have hne' : (c : ℂ) + y * I - x ≠ 0 := sub_ne_zero.mpr hne
    have hcp : ((c + p : ℝ) : ℂ) = x := by rw [← hxcp]
    have hcm : ((c - p : ℝ) : ℂ) = a := by rw [ha_def]
    rw [hcp, hcm]
    simp only [hH]
    rw [dslope_of_ne _ hne, slope_def_field]
    field_simp
    ring
  simp_rw [hdecomp]
  rw [integral_add hHint (hKint.const_mul _), hHzero, integral_const_mul, hKval]
  ring

/-- Derivative of `x ↦ ((w - x)^s)⁻¹` (real variable `x`, `w - x ≠ 0`). -/
theorem hasDerivAt_inv_sub_pow (w : ℂ) (s : ℕ) {x : ℝ} (hx : w - x ≠ 0) :
    HasDerivAt (fun x : ℝ => ((w - x) ^ s)⁻¹) ((s : ℂ) * ((w - x) ^ (s + 1))⁻¹) x := by
  have h1 : HasDerivAt (fun x : ℝ => w - (x : ℂ)) (-1) x := by
    have := ((hasDerivAt_id x).ofReal_comp).const_sub w
    simpa using this
  have h3 := (hasDerivAt_zpow (-(s : ℤ)) (w - x) (Or.inl hx)).comp x h1
  have hfun : ((fun z : ℂ => z ^ (-(s : ℤ))) ∘ fun x : ℝ => w - (x : ℂ)) =
      fun x : ℝ => ((w - x) ^ s)⁻¹ := by
    funext y
    simp [zpow_neg, zpow_natCast]
  rw [hfun] at h3
  convert h3 using 1
  have he : (-(s : ℤ) - 1) = -((s + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [he, zpow_neg, zpow_natCast]
  push_cast
  ring

/-- **Differentiation under the integral sign** for the kernels `(c + iy - x)^{-s}`. -/
theorem hasDerivAt_vline_integral {g : ℝ → ℂ} (hg : Integrable g) (hgc : Continuous g)
    {c x₀ : ℝ} (hx₀ : x₀ ≠ c) (s : ℕ) :
    HasDerivAt (fun x : ℝ => ∫ y : ℝ, g y * (((c : ℂ) + y * I - x) ^ s)⁻¹)
      ((s : ℂ) * ∫ y : ℝ, g y * (((c : ℂ) + y * I - x₀) ^ (s + 1))⁻¹) x₀ := by
  set δ : ℝ := |x₀ - c| / 2 with hδ
  have hδpos : 0 < δ := by
    rw [hδ]; have : 0 < |x₀ - c| := abs_pos.mpr (sub_ne_zero.mpr hx₀); linarith
  have hne : ∀ x : ℝ, x ≠ c → ∀ y : ℝ, (c : ℂ) + y * I - x ≠ 0 := by
    intro x hx y h
    have := congrArg Complex.re h
    simp at this
    exact hx (by linarith)
  have hnorm_ge : ∀ x y : ℝ, |c - x| ≤ ‖(c : ℂ) + y * I - x‖ := by
    intro x y
    have := Complex.abs_re_le_norm ((c : ℂ) + y * I - x)
    simpa using this
  have hball : ∀ x ∈ Metric.ball x₀ δ, δ ≤ |c - x| := by
    intro x hx
    rw [Metric.mem_ball, Real.dist_eq] at hx
    have h1 : |x₀ - c| ≤ |x₀ - x| + |x - c| := by
      have := abs_sub_le x₀ x c; linarith
    rw [abs_sub_comm x₀ x] at h1
    rw [abs_sub_comm c x]
    rw [hδ] at hx ⊢
    linarith
  have hcont : ∀ x : ℝ, x ≠ c → ∀ k : ℕ,
      Continuous fun y : ℝ => g y * (((c : ℂ) + y * I - x) ^ k)⁻¹ := by
    intro x hx k
    exact hgc.mul (Continuous.inv₀ (by fun_prop) fun y => pow_ne_zero _ (hne x hx y))
  set F : ℝ → ℝ → ℂ := fun x y => g y * (((c : ℂ) + y * I - x) ^ s)⁻¹ with hF
  set F' : ℝ → ℝ → ℂ := fun x y => g y * ((s : ℂ) * (((c : ℂ) + y * I - x) ^ (s + 1))⁻¹)
    with hF'
  have hmeas : ∀ᶠ x in 𝓝 x₀, AEStronglyMeasurable (F x) volume := by
    filter_upwards [eventually_ne_nhds hx₀] with x hx
    exact (hcont x hx s).aestronglyMeasurable
  have hFint : Integrable (F x₀) volume := by
    refine (hg.norm.mul_const ((|c - x₀|)⁻¹ ^ s)).mono' (hcont x₀ hx₀ s).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    simp only [hF]
    rw [norm_mul, norm_inv, norm_pow]
    gcongr
    rw [← inv_pow]
    have hpos : 0 < |c - x₀| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hx₀))
    gcongr
    exact hnorm_ge x₀ y
  have hF'meas : AEStronglyMeasurable (F' x₀) volume := by
    have := (hcont x₀ hx₀ (s + 1)).const_mul (s : ℂ)
    refine (this.aestronglyMeasurable).congr (Eventually.of_forall fun y => ?_)
    simp only [hF']
    ring
  set bound : ℝ → ℝ := fun y => ‖g y‖ * ((s : ℝ) * (δ⁻¹) ^ (s + 1)) with hbound
  have hbound_int : Integrable bound volume := hg.norm.mul_const _
  have hbnd : ∀ᵐ y ∂volume, ∀ x ∈ Metric.ball x₀ δ, ‖F' x y‖ ≤ bound y := by
    refine Eventually.of_forall fun y x hx => ?_
    simp only [hF', hbound]
    rw [norm_mul, norm_mul, norm_inv, norm_pow, Complex.norm_natCast]
    gcongr
    rw [← inv_pow]
    gcongr
    exact le_trans (hball x hx) (hnorm_ge x y)
  have hdiff : ∀ᵐ y ∂volume, ∀ x ∈ Metric.ball x₀ δ,
      HasDerivAt (fun x => F x y) (F' x y) x := by
    refine Eventually.of_forall fun y x hx => ?_
    have hxc : x ≠ c := by
      intro h; have := hball x hx; rw [h, sub_self, abs_zero] at this; linarith
    simp only [hF, hF']
    exact (hasDerivAt_inv_sub_pow _ s (hne x hxc y)).const_mul (g y)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (Metric.ball_mem_nhds x₀ hδpos)
    hmeas hFint hF'meas hbnd hbound_int hdiff
  convert key.2 using 1
  simp only [hF']
  rw [← integral_const_mul]
  congr 1
  ext y
  ring

/-- Vanishing when the pole is to the left of the line. -/
theorem vline_left {F : ℂ → ℂ} {c c' : ℝ} (hcc : c' < c)
    (hF : DifferentiableOn ℂ F {t | c' < t.re}) {C r : ℝ} (hr : 1 ≤ r) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℂ, c ≤ t.re → r ≤ ‖t‖ → ‖F t‖ ≤ C / ‖t‖) {x : ℝ} (hx : x < c) {s : ℕ}
    (hs : 1 ≤ s) :
    ∫ y : ℝ, F (c + y * I) * (((c : ℂ) + y * I - x) ^ s)⁻¹ = 0 := by
  set c'' : ℝ := max c' x
  have hc''c : c'' < c := max_lt hcc hx
  have hdiff : DifferentiableOn ℂ (fun t => F t * ((t - x) ^ s)⁻¹) {t | c'' < t.re} := by
    refine DifferentiableOn.mul (hF.mono fun t ht => ?_) ?_
    · show c' < t.re
      exact lt_of_le_of_lt (le_max_left _ _) ht
    refine DifferentiableOn.inv (DifferentiableOn.pow (differentiableOn_id.sub
      (differentiableOn_const _)) s) ?_
    intro t ht h
    have h1 : t - x = 0 := (pow_eq_zero_iff (by omega)).mp h
    have := congrArg Complex.re h1
    simp at this
    have h2 : c'' < t.re := ht
    have : x ≤ c'' := le_max_right _ _
    linarith
  set r₁ : ℝ := max r (2 * |x| + 1)
  have hr₁ : 1 ≤ r₁ := le_trans hr (le_max_left _ _)
  have hdec : ∀ t : ℂ, c ≤ t.re → r₁ ≤ ‖t‖ →
      ‖F t * ((t - x) ^ s)⁻¹‖ ≤ (C * 2 ^ s) / ‖t‖ ^ 2 := by
    intro t htre htn
    have htr : r ≤ ‖t‖ := le_trans (le_max_left _ _) htn
    have ht2 : 2 * |x| + 1 ≤ ‖t‖ := le_trans (le_max_right _ _) htn
    have ht1 : 1 ≤ ‖t‖ := by linarith [abs_nonneg x]
    have htpos : 0 < ‖t‖ := by linarith
    have hx2 : ‖t‖ / 2 ≤ ‖t - x‖ := by
      have := norm_sub_norm_le t (x : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs] at this
      linarith
    have hx2pos : 0 < ‖t‖ / 2 := by positivity
    rw [norm_mul, norm_inv, norm_pow]
    calc ‖F t‖ * (‖t - ↑x‖ ^ s)⁻¹ ≤ C / ‖t‖ * ((‖t‖ / 2) ^ s)⁻¹ := by
          gcongr
          exact hC t htre htr
      _ = C * 2 ^ s / ‖t‖ / ‖t‖ ^ s := by
          rw [div_pow]; field_simp
      _ ≤ C * 2 ^ s / ‖t‖ / ‖t‖ := by
          gcongr
          calc ‖t‖ = ‖t‖ ^ 1 := (pow_one _).symm
            _ ≤ ‖t‖ ^ s := pow_le_pow_right₀ ht1 hs
      _ = C * 2 ^ s / ‖t‖ ^ 2 := by ring
  exact (vline_integral_eq_zero hc''c hdiff hr₁ (by positivity) hdec).2

/-- **Cauchy's formula for higher-order poles**, by differentiating the simple-pole formula.
`D j` is the `j`-th Taylor coefficient function (`D 0 = F`, `D j' = (j+1) D (j+1)` on `x > c`). -/
theorem vline_higher {F : ℂ → ℂ} {c c' : ℝ} (hcc : c' < c)
    (hF : DifferentiableOn ℂ F {t | c' < t.re}) {C r : ℝ} (hr : 1 ≤ r) (hC0 : 0 ≤ C)
    (hC : ∀ t : ℂ, c ≤ t.re → r ≤ ‖t‖ → ‖F t‖ ≤ C / ‖t‖)
    (hg : Integrable (fun y : ℝ => F (c + y * I)))
    (D : ℕ → ℝ → ℂ) (hD0 : ∀ x : ℝ, c < x → D 0 x = F x)
    (hD : ∀ (j : ℕ) (x : ℝ), c < x → HasDerivAt (D j) (((j : ℂ) + 1) * D (j + 1) x) x) :
    ∀ (j : ℕ) (x : ℝ), c < x →
      ∫ y : ℝ, F (c + y * I) * (((c : ℂ) + y * I - x) ^ (j + 1))⁻¹ = -2 * π * D j x := by
  have hgc : Continuous fun y : ℝ => F (c + y * I) := by
    refine hF.continuousOn.comp_continuous (continuous_vline c) fun y => ?_
    show c' < ((c : ℂ) + (y : ℂ) * I).re
    rw [vline_re]; exact hcc
  intro j
  induction j with
  | zero =>
    intro x hx
    simp only [zero_add, pow_one]
    rw [vline_cauchy hcc hF hr hC0 hC hx, hD0 x hx]
  | succ j ih =>
    intro x hx
    have hxne : x ≠ c := ne_of_gt hx
    have h1 := hasDerivAt_vline_integral hg hgc hxne (j + 1)
    have heq : (fun x : ℝ => ∫ y : ℝ, F (c + y * I) * (((c : ℂ) + y * I - x) ^ (j + 1))⁻¹)
        =ᶠ[𝓝 x] fun x => -2 * π * D j x := by
      filter_upwards [Ioi_mem_nhds hx] with x' hx'
      exact ih x' hx'
    have h2 : HasDerivAt (fun x => -2 * π * D j x)
        (((j + 1 : ℕ) : ℂ) *
          ∫ y : ℝ, F (c + y * I) * (((c : ℂ) + y * I - x) ^ (j + 1 + 1))⁻¹) x :=
      h1.congr_of_eventuallyEq heq.symm
    have h3 : HasDerivAt (fun x => -2 * π * D j x)
        (-2 * π * (((j : ℂ) + 1) * D (j + 1) x)) x := (hD j x hx).const_mul _
    have h4 := h2.unique h3
    have hj : ((j : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero j
    push_cast at h4
    have : ((j : ℂ) + 1) * ∫ y : ℝ, F (c + y * I) * (((c : ℂ) + y * I - x) ^ (j + 1 + 1))⁻¹ =
        ((j : ℂ) + 1) * (-2 * π * D (j + 1) x) := by
      rw [h4]; ring
    exact mul_left_cancel₀ hj this

/-- Reduction to the upper half of the line for conjugation-symmetric integrands. -/
theorem integral_line_conj {f : ℂ → ℂ} {c : ℝ} (hf : ∀ t, f ((starRingEnd ℂ) t) = (starRingEnd ℂ) (f t))
    (hint : Integrable (fun y : ℝ => f (c + y * I))) :
    ∫ y : ℝ, f (c + y * I) =
      (∫ y in Ioi (0 : ℝ), f (c + y * I)) + (starRingEnd ℂ) (∫ y in Ioi (0 : ℝ), f (c + y * I)) := by
  rw [← intervalIntegral.integral_Iic_add_Ioi hint.integrableOn hint.integrableOn, add_comm]
  congr 1
  have h1 : ∫ y in Iic (0 : ℝ), f (c + y * I) = ∫ y in Ioi (0 : ℝ), f (c + (-y : ℝ) * I) := by
    rw [integral_comp_neg_Ioi (c := 0) (f := fun y : ℝ => f (c + y * I)), neg_zero]
  rw [h1, ← integral_conj]
  congr 1
  ext y
  rw [← hf]
  congr 1
  apply Complex.ext <;> simp

theorem norm_integral_line_conj_le {f : ℂ → ℂ} {c : ℝ}
    (hf : ∀ t, f ((starRingEnd ℂ) t) = (starRingEnd ℂ) (f t))
    (hint : Integrable (fun y : ℝ => f (c + y * I))) :
    ‖∫ y : ℝ, f (c + y * I)‖ ≤ 2 * ‖∫ y in Ioi (0 : ℝ), f (c + y * I)‖ := by
  rw [integral_line_conj hf hint]
  refine le_trans (norm_add_le _ _) ?_
  rw [Complex.norm_conj]
  linarith

/-- **Contour shift in a half-strip** `a ≤ Re t ≤ b`, `Im t ≥ 1`. -/
theorem halfstrip_shift {f : ℂ → ℂ} {a b : ℝ} (hab : a ≤ b)
    (hf : DifferentiableOn ℂ f {t | 0 < t.im})
    (hia : IntegrableOn (fun y : ℝ => f (a + y * I)) (Ioi 1))
    (hib : IntegrableOn (fun y : ℝ => f (b + y * I)) (Ioi 1))
    (htop : Tendsto (fun Y : ℝ => ∫ x in a..b, f (x + Y * I)) atTop (𝓝 0)) :
    I * ∫ y in Ioi (1 : ℝ), f (a + y * I) =
      (∫ x in a..b, f (x + (1 : ℝ) * I)) + I * ∫ y in Ioi (1 : ℝ), f (b + y * I) := by
  have hrect : ∀ Y : ℝ, 1 ≤ Y →
      (((∫ x in a..b, f (x + (1 : ℝ) * I)) - ∫ x in a..b, f (x + Y * I)) +
        I • ∫ y in (1 : ℝ)..Y, f (b + y * I)) - I • ∫ y in (1 : ℝ)..Y, f (a + y * I) = 0 := by
    intro Y hY
    have hsub : Set.uIcc (a : ℝ) b ×ℂ Set.uIcc (1 : ℝ) Y ⊆ {t : ℂ | 0 < t.im} := by
      intro t ht
      rw [Complex.mem_reProdIm, Set.uIcc_of_le hY] at ht
      show 0 < t.im
      linarith [ht.2.1]
    have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn f ⟨a, 1⟩ ⟨b, Y⟩
      (hf.mono hsub)
    simpa using this
  have hlim : Tendsto (fun Y : ℝ => (((∫ x in a..b, f (x + (1 : ℝ) * I)) -
      ∫ x in a..b, f (x + Y * I)) + I • ∫ y in (1 : ℝ)..Y, f (b + y * I)) -
        I • ∫ y in (1 : ℝ)..Y, f (a + y * I)) atTop
      (𝓝 ((((∫ x in a..b, f (x + (1 : ℝ) * I)) - 0) + I • ∫ y in Ioi (1 : ℝ), f (b + y * I)) -
        I • ∫ y in Ioi (1 : ℝ), f (a + y * I))) := by
    refine ((tendsto_const_nhds.sub htop).add ?_).sub ?_
    · exact (intervalIntegral_tendsto_integral_Ioi 1 hib tendsto_id).const_smul I
    · exact (intervalIntegral_tendsto_integral_Ioi 1 hia tendsto_id).const_smul I
  have hzero : Tendsto (fun Y : ℝ => (((∫ x in a..b, f (x + (1 : ℝ) * I)) -
      ∫ x in a..b, f (x + Y * I)) + I • ∫ y in (1 : ℝ)..Y, f (b + y * I)) -
        I • ∫ y in (1 : ℝ)..Y, f (a + y * I)) atTop (𝓝 0) := by
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
    exact (hrect Y hY).symm
  have := tendsto_nhds_unique hlim hzero
  rw [sub_zero, sub_eq_zero] at this
  rw [smul_eq_mul, smul_eq_mul] at this
  rw [← this]


/-! ## Half-integer kernels -/

/-- The half-integer points `x_ν = ν + 1/2`. -/
def hpt (ν : ℤ) : ℂ := (ν : ℂ) + 1 / 2

/-- The kernel `K_s(t) = ∑_{ν ∈ ℤ} (t - (ν + 1/2))^{-s}`. -/
def kerS (s : ℕ) (t : ℂ) : ℂ := ∑' ν : ℤ, ((t - hpt ν) ^ s)⁻¹

theorem summable_norm_inv_int_add_pow (a : ℂ) {s : ℕ} (hs : 2 ≤ s) :
    Summable fun ν : ℤ => ‖(((ν : ℂ) + a) ^ s)⁻¹‖ := by
  have h1 := (Real.summable_one_div_int_add_rpow a.re (s : ℝ)).mpr (by
    have : (2 : ℝ) ≤ s := by exact_mod_cast hs
    linarith)
  refine Summable.of_norm_bounded_eventually h1 ?_
  rw [Filter.eventually_cofinite]
  refine Set.Subsingleton.finite ?_
  have hsub : {x : ℤ | ¬‖‖(((x : ℂ) + a) ^ s)⁻¹‖‖ ≤ 1 / |(x : ℝ) + a.re| ^ (s : ℝ)} ⊆
      {x : ℤ | (x : ℝ) + a.re = 0} := by
    intro x hx
    simp only [Set.mem_ofPred_eq] at hx ⊢
    by_contra hne
    apply hx
    rw [norm_norm, norm_inv, norm_pow, Real.rpow_natCast, one_div]
    have hpos : 0 < |(x : ℝ) + a.re| := abs_pos.mpr hne
    have hle : |(x : ℝ) + a.re| ≤ ‖(x : ℂ) + a‖ := by
      have := Complex.abs_re_le_norm ((x : ℂ) + a)
      simpa using this
    gcongr
  refine Set.Subsingleton.anti ?_ hsub
  intro x hx y hy
  simp only [Set.mem_ofPred_eq] at hx hy
  have : (x : ℝ) = y := by linarith
  exact_mod_cast this

theorem summable_norm_kerS_term (t : ℂ) {s : ℕ} (hs : 2 ≤ s) :
    Summable fun ν : ℤ => ‖((t - hpt ν) ^ s)⁻¹‖ := by
  have := summable_norm_inv_int_add_pow (1 / 2 - t) hs
  refine this.congr fun ν => ?_
  rw [norm_inv, norm_inv, norm_pow, norm_pow]
  congr 1
  rw [← norm_neg]
  congr 1
  simp only [hpt]
  ring

theorem summable_kerS_term (t : ℂ) {s : ℕ} (hs : 2 ≤ s) :
    Summable fun ν : ℤ => ((t - hpt ν) ^ s)⁻¹ :=
  (summable_norm_kerS_term t hs).of_norm

/-- `Z_s^{abs} = ∑_ν |ν + 1/2|^{-s}`. -/
def zabs (s : ℕ) : ℝ := ∑' ν : ℤ, ‖((hpt ν) ^ s)⁻¹‖

theorem hpt_eq_ofReal (k : ℤ) : hpt k = (((k : ℝ) + 1 / 2 : ℝ) : ℂ) := by
  simp only [hpt]; push_cast; ring

theorem norm_hpt (k : ℤ) : ‖hpt k‖ = |(k : ℝ) + 1 / 2| := by
  rw [hpt_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]

theorem half_le_norm_hpt (k : ℤ) : (1 / 2 : ℝ) ≤ ‖hpt k‖ := by
  rw [norm_hpt]
  rcases le_or_gt 0 k with hk | hk
  · have : (0 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    rw [abs_of_nonneg (by linarith)]
    linarith
  · have : (k : ℝ) ≤ -1 := by
      have : k ≤ -1 := by omega
      exact_mod_cast this
    rw [abs_of_neg (by linarith)]
    linarith

theorem norm_sub_hpt_ge_of_int (c : ℤ) (y : ℝ) (ν : ℤ) :
    ‖hpt (c - 1 - ν)‖ ≤ ‖(c : ℂ) + (y : ℂ) * I - hpt ν‖ := by
  have h1 := Complex.abs_re_le_norm ((c : ℂ) + (y : ℂ) * I - hpt ν)
  have hre : ((c : ℂ) + (y : ℂ) * I - hpt ν).re = (c : ℝ) - ν - 1 / 2 := by
    rw [hpt_eq_ofReal]
    simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, Complex.intCast_re]
    ring
  rw [hre] at h1
  rw [norm_hpt]
  have : ((c - 1 - ν : ℤ) : ℝ) + 1 / 2 = (c : ℝ) - ν - 1 / 2 := by push_cast; ring
  rw [this]
  exact h1

/-- On a vertical line through an integer, `‖K_s‖ ≤ ∑_ν |ν + 1/2|^{-s}`. -/
theorem norm_kerS_vline_le {s : ℕ} (hs : 2 ≤ s) (c : ℤ) (y : ℝ) :
    ‖kerS s ((c : ℂ) + (y : ℂ) * I)‖ ≤ zabs s := by
  unfold kerS zabs
  refine le_trans (norm_tsum_le_tsum_norm (summable_norm_kerS_term _ hs)) ?_
  have hsum0 : Summable fun ν : ℤ => ‖((hpt ν) ^ s)⁻¹‖ := by
    have := summable_norm_kerS_term 0 hs
    refine this.congr fun ν => ?_
    rw [norm_inv, norm_inv, norm_pow, norm_pow, zero_sub, norm_neg]
  have hsum1 : Summable fun ν : ℤ => ‖((hpt (c - 1 - ν)) ^ s)⁻¹‖ := by
    have := (Equiv.summable_iff (Equiv.subLeft (c - 1))
      (f := fun ν : ℤ => ‖((hpt ν) ^ s)⁻¹‖)).mpr hsum0
    simpa only [Function.comp_def, Equiv.subLeft_apply] using this
  calc ∑' ν : ℤ, ‖(((c : ℂ) + (y : ℂ) * I - hpt ν) ^ s)⁻¹‖
      ≤ ∑' ν : ℤ, ‖((hpt (c - 1 - ν)) ^ s)⁻¹‖ := by
        refine Summable.tsum_le_tsum (fun ν => ?_) (summable_norm_kerS_term _ hs) hsum1
        rw [norm_inv, norm_inv, norm_pow, norm_pow]
        have hpos : 0 < ‖hpt (c - 1 - ν)‖ := lt_of_lt_of_le (by norm_num) (half_le_norm_hpt _)
        gcongr
        exact norm_sub_hpt_ge_of_int c y ν
    _ = ∑' ν : ℤ, ‖((hpt ν) ^ s)⁻¹‖ := by
        have e := (Equiv.subLeft (c - 1)).tsum_eq (fun ν => ‖((hpt ν) ^ s)⁻¹‖)
        simp only [Equiv.subLeft_apply] at e
        exact e

/-- Conjugation symmetry of the kernel. -/
theorem kerS_conj (s : ℕ) (t : ℂ) : kerS s ((starRingEnd ℂ) t) = (starRingEnd ℂ) (kerS s t) := by
  unfold kerS
  rw [Complex.conj_tsum]
  congr 1
  ext ν
  rw [map_inv₀, map_pow, map_sub, hpt_eq_ofReal, Complex.conj_ofReal]

/-- Differentiability of the kernel on a ball staying away from the half-integers. -/
theorem kerS_differentiableOn_ball {s : ℕ} (hs : 2 ≤ s) (t₀ : ℂ) {r : ℝ} (hr : 0 < r)
    (h : ∀ ν : ℤ, 2 * r ≤ ‖t₀ - hpt ν‖) : DifferentiableOn ℂ (kerS s) (Metric.ball t₀ r) := by
  unfold kerS
  refine differentiableOn_tsum_of_summable_norm
    ((summable_norm_kerS_term t₀ hs).mul_left (2 ^ s)) (fun ν => ?_) Metric.isOpen_ball
    (fun ν w hw => ?_)
  · refine DifferentiableOn.inv (DifferentiableOn.pow (differentiableOn_id.sub
      (differentiableOn_const _)) s) fun w hw h0 => ?_
    have h1 : w - hpt ν = 0 := (pow_eq_zero_iff (by omega)).mp h0
    rw [Metric.mem_ball, dist_eq_norm] at hw
    have h2 := h ν
    have : ‖t₀ - hpt ν‖ ≤ ‖w - t₀‖ := by
      have : t₀ - hpt ν = -(w - t₀) + (w - hpt ν) := by ring
      rw [this, h1, add_zero, norm_neg]
    linarith
  · rw [Metric.mem_ball, dist_eq_norm] at hw
    have h2 := h ν
    have hge : ‖t₀ - hpt ν‖ / 2 ≤ ‖w - hpt ν‖ := by
      have : ‖t₀ - hpt ν‖ ≤ ‖w - hpt ν‖ + ‖w - t₀‖ := by
        have : t₀ - hpt ν = (w - hpt ν) - (w - t₀) := by ring
        rw [this]; exact norm_sub_le _ _
      linarith
    have hpos : 0 < ‖t₀ - hpt ν‖ / 2 := by linarith
    rw [norm_inv, norm_inv, norm_pow, norm_pow]
    calc (‖w - hpt ν‖ ^ s)⁻¹ ≤ ((‖t₀ - hpt ν‖ / 2) ^ s)⁻¹ := by gcongr
      _ = 2 ^ s * (‖t₀ - hpt ν‖ ^ s)⁻¹ := by rw [div_pow]; field_simp

theorem kerS_differentiableOn_upper {s : ℕ} (hs : 2 ≤ s) :
    DifferentiableOn ℂ (kerS s) {t | 0 < t.im} := by
  intro t₀ ht₀
  have ht₀' : 0 < t₀.im := ht₀
  have hball := kerS_differentiableOn_ball hs t₀ (r := t₀.im / 2) (by linarith) fun ν => by
    have := Complex.abs_im_le_norm (t₀ - hpt ν)
    have him : (t₀ - hpt ν).im = t₀.im := by simp [hpt]
    rw [him, abs_of_pos ht₀'] at this
    linarith
  exact (hball.differentiableAt (Metric.ball_mem_nhds t₀ (by linarith))).differentiableWithinAt

theorem kerS_differentiableAt_vline {s : ℕ} (hs : 2 ≤ s) (c : ℤ) (y : ℝ) :
    DifferentiableAt ℂ (kerS s) ((c : ℂ) + (y : ℂ) * I) := by
  have hball := kerS_differentiableOn_ball hs ((c : ℂ) + (y : ℂ) * I) (r := 1 / 4) (by norm_num)
    fun ν => by
      have h1 := norm_sub_hpt_ge_of_int c y ν
      have h2 := half_le_norm_hpt (c - 1 - ν)
      linarith
  exact hball.differentiableAt (Metric.ball_mem_nhds _ (by norm_num))

/-- **Exponential decay** of the kernel in the upper half-plane (q-expansion). -/
theorem kerS_decay {s : ℕ} (hs : 2 ≤ s) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ t : ℂ, 1 ≤ t.im → ‖kerS s t‖ ≤ κ * Real.exp (-2 * π * t.im) := by
  obtain ⟨k, rfl⟩ : ∃ k, s = k + 1 := ⟨s - 1, by omega⟩
  have hk : 1 ≤ k := by omega
  set ρ₀ : ℝ := Real.exp (-2 * π) with hρ₀
  have hρ₀pos : 0 < ρ₀ := Real.exp_pos _
  have hρ₀lt : ρ₀ < 1 := by
    rw [hρ₀]; exact Real.exp_lt_one_iff.mpr (by linarith [Real.pi_pos])
  have hsum0 : Summable fun d : ℕ => (d : ℝ) ^ k * ρ₀ ^ d :=
    summable_pow_mul_geometric_of_norm_lt_one k (by rw [Real.norm_eq_abs, abs_of_pos hρ₀pos]; exact hρ₀lt)
  set S₀ : ℝ := ∑' d : ℕ, (d : ℝ) ^ k * ρ₀ ^ d
  have hS₀ : 0 ≤ S₀ := tsum_nonneg fun d => by positivity
  refine ⟨(2 * π) ^ (k + 1) / (k.factorial : ℝ) * (S₀ / ρ₀), by positivity, fun t ht => ?_⟩
  have htpos : 0 < (t - 1 / 2).im := by simp; linarith
  set z : UpperHalfPlane := ⟨t - 1 / 2, htpos⟩
  have hz : (z : ℂ) = t - 1 / 2 := rfl
  have hq := EisensteinSeries.qExpansion_identity hk z
  have hker : kerS (k + 1) t = ∑' n : ℤ, 1 / ((z : ℂ) + n) ^ (k + 1) := by
    unfold kerS
    rw [← (Equiv.neg ℤ).tsum_eq]
    congr 1
    ext n
    simp only [Equiv.neg_apply, hpt, hz, one_div]
    congr 2
    push_cast
    ring
  rw [hker, hq]
  set ρ : ℝ := Real.exp (-2 * π * t.im) with hρ
  have hqn : ‖Complex.exp (2 * π * I * (z : ℂ))‖ = ρ := by
    rw [Complex.norm_exp, hz, hρ]
    congr 1
    simp only [Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im, Complex.re_ofNat, Complex.im_ofNat]
    norm_num
  have hρle : ρ ≤ ρ₀ := by
    rw [hρ, hρ₀]; apply Real.exp_le_exp.mpr
    nlinarith [Real.pi_pos]
  have hρpos : 0 < ρ := Real.exp_pos _
  have hsum1 : Summable fun d : ℕ => ‖(d : ℂ) ^ k * Complex.exp (2 * π * I * (z : ℂ)) ^ d‖ := by
    have : Summable fun d : ℕ => (d : ℝ) ^ k * ρ ^ d :=
      summable_pow_mul_geometric_of_norm_lt_one k
        (by rw [Real.norm_eq_abs, abs_of_pos hρpos]; linarith)
    refine this.congr fun d => ?_
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast, hqn]
  rw [norm_mul]
  have hcoef : ‖(-2 * (π : ℂ) * I) ^ (k + 1) / (k.factorial : ℂ)‖ =
      (2 * π) ^ (k + 1) / (k.factorial : ℝ) := by
    rw [norm_div, norm_pow, Complex.norm_natCast]
    congr 2
    rw [norm_mul, norm_mul, Complex.norm_I, mul_one, norm_neg, Complex.norm_ofNat,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos]
  rw [hcoef, show (2 * π) ^ (k + 1) / (k.factorial : ℝ) * (S₀ / ρ₀) * ρ =
    (2 * π) ^ (k + 1) / (k.factorial : ℝ) * (S₀ / ρ₀ * ρ) by ring]
  have hA : 0 ≤ (2 * π) ^ (k + 1) / (k.factorial : ℝ) := by positivity
  refine mul_le_mul_of_nonneg_left ?_ hA
  refine le_trans (norm_tsum_le_tsum_norm hsum1) ?_
  have hterm : ∀ d : ℕ, ‖(d : ℂ) ^ k * Complex.exp (2 * π * I * (z : ℂ)) ^ d‖ ≤
      (S₀ / ρ₀ * ρ) * 0 + (ρ / ρ₀) * ((d : ℝ) ^ k * ρ₀ ^ d) := by
    intro d
    rw [norm_mul, norm_pow, norm_pow, Complex.norm_natCast, hqn, mul_zero, zero_add]
    rcases d with _ | d
    · have hk0 : k ≠ 0 := by omega
      simp [hk0]
    · rw [pow_succ, pow_succ]
      have : ρ ^ d ≤ ρ₀ ^ d := pow_le_pow_left₀ hρpos.le hρle d
      have h2 : ((d + 1 : ℕ) : ℝ) ^ k * (ρ ^ d * ρ) ≤ ((d + 1 : ℕ) : ℝ) ^ k * (ρ₀ ^ d * ρ) := by
        gcongr
      calc ((d + 1 : ℕ) : ℝ) ^ k * (ρ ^ d * ρ) ≤ ((d + 1 : ℕ) : ℝ) ^ k * (ρ₀ ^ d * ρ) := h2
        _ = ρ / ρ₀ * (((d + 1 : ℕ) : ℝ) ^ k * (ρ₀ ^ d * ρ₀)) := by field_simp
  calc ∑' d : ℕ, ‖(d : ℂ) ^ k * Complex.exp (2 * π * I * (z : ℂ)) ^ d‖
      ≤ ∑' d : ℕ, ((S₀ / ρ₀ * ρ) * 0 + (ρ / ρ₀) * ((d : ℝ) ^ k * ρ₀ ^ d)) :=
        Summable.tsum_le_tsum hterm hsum1 ((hsum0.mul_left (ρ / ρ₀)).congr fun d => by ring)
    _ = (ρ / ρ₀) * S₀ := by
        simp only [mul_zero, zero_add]
        rw [tsum_mul_left]
    _ = S₀ / ρ₀ * ρ := by ring


/-! ## Pair algebra -/

/-- `a(i,j) = (-1)^j C(i+j-1, j)`: `(x+ε)^{-i} = ∑_j a(i,j) x^{-(i+j)} ε^j`. -/
def acoef (i j : ℕ) : ℚ := (-1) ^ j * (((i + j - 1).choose j : ℕ) : ℚ)

theorem acoef_zero (i : ℕ) : acoef i 0 = 1 := by simp [acoef]

theorem acoef_succ (i j : ℕ) (hi : 1 ≤ i) :
    acoef i j * (-((i + j : ℕ) : ℚ)) = ((j : ℚ) + 1) * acoef i (j + 1) := by
  unfold acoef
  obtain ⟨N, hN1, hN2⟩ : ∃ N, i + j - 1 = N ∧ i + j = N + 1 := ⟨i + j - 1, rfl, by omega⟩
  have h1 : i + (j + 1) - 1 = N + 1 := by omega
  rw [hN1, h1, hN2]
  have h2 : ((N + 1 : ℕ) : ℚ) * ((N.choose j : ℕ) : ℚ) =
      (((N + 1).choose (j + 1) : ℕ) : ℚ) * ((j : ℚ) + 1) := by
    exact_mod_cast Nat.add_one_mul_choose_eq N j
  rw [pow_succ]
  linear_combination (-(-1 : ℚ) ^ j) * h2

/-- `D_j(z) = ∑_{i,k} r_{i,k} a(i,j) (z+k)^{-(i+j)}` (`j`-th Taylor coefficient of `R_n` at `z`). -/
def Dc (n : ℕ) (h : Fin 6 → ℤ) (j : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ Icc 1 6, ∑ k ∈ range (n + 1),
    (rcoef n h i k : ℂ) * (acoef i j : ℂ) * ((z + k) ^ (i + j))⁻¹

/-- The partial-fraction form `∑_{i,k} r_{i,k} (t+k)^{-i}` of `R_n`. -/
def Pc (n : ℕ) (h : Fin 6 → ℤ) (t : ℂ) : ℂ :=
  ∑ i ∈ Icc 1 6, ∑ k ∈ range (n + 1), (rcoef n h i k : ℂ) * ((t + k) ^ i)⁻¹

/-- The product form of `R_n` as a complex function. -/
def Rc (n : ℕ) (h : Fin 6 → ℤ) (t : ℂ) : ℂ :=
  (2 * t + n) * (∏ p : Fin 6, ∏ u ∈ offsets n (h p), (t + 1 / 2 + u)) /
    (∏ j ∈ range (n + 1), (t + j)) ^ 6

theorem Pc_eq_Dc_zero (n : ℕ) (h : Fin 6 → ℤ) (t : ℂ) : Pc n h t = Dc n h 0 t := by
  simp [Pc, Dc, acoef_zero]

theorem hasDerivAt_inv_add_pow (k : ℂ) (N : ℕ) {z : ℂ} (hz : z + k ≠ 0) :
    HasDerivAt (fun z => ((z + k) ^ N)⁻¹) (-(N : ℂ) * ((z + k) ^ (N + 1))⁻¹) z := by
  have h1 : HasDerivAt (fun z : ℂ => z + k) 1 z := (hasDerivAt_id z).add_const k
  have h3 := (hasDerivAt_zpow (-(N : ℤ)) (z + k) (Or.inl hz)).comp z h1
  have hfun : ((fun w : ℂ => w ^ (-(N : ℤ))) ∘ fun z : ℂ => z + k) =
      fun z : ℂ => ((z + k) ^ N)⁻¹ := by
    funext y
    simp [zpow_neg, zpow_natCast]
  rw [hfun] at h3
  convert h3 using 1
  have he : (-(N : ℤ) - 1) = -((N + 1 : ℕ) : ℤ) := by push_cast; ring
  rw [he, zpow_neg, zpow_natCast]
  push_cast
  ring

theorem Dc_hasDerivAt (n : ℕ) (h : Fin 6 → ℤ) (j : ℕ) {z : ℂ} (hz : ∀ k ≤ n, z + k ≠ 0) :
    HasDerivAt (Dc n h j) (((j : ℂ) + 1) * Dc n h (j + 1) z) z := by
  have hD : HasDerivAt (Dc n h j) (∑ i ∈ Icc 1 6, ∑ k ∈ range (n + 1),
      (rcoef n h i k : ℂ) * (acoef i j : ℂ) *
        (-((i + j : ℕ) : ℂ) * ((z + k) ^ (i + j + 1))⁻¹)) z := by
    unfold Dc
    apply HasDerivAt.fun_sum
    intro i _
    apply HasDerivAt.fun_sum
    intro k hk
    exact (hasDerivAt_inv_add_pow (k : ℂ) (i + j) (hz k (by simpa [Nat.lt_succ_iff] using hk))).const_mul _
  convert hD using 1
  unfold Dc
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hc := acoef_succ i j (Finset.mem_Icc.1 hi).1
  have hc' : ((acoef i j : ℚ) : ℂ) * (-((i + j : ℕ) : ℂ)) =
      ((j : ℂ) + 1) * ((acoef i (j + 1) : ℚ) : ℂ) := by exact_mod_cast hc
  rw [show i + (j + 1) = i + j + 1 by ring]
  linear_combination (-(rcoef n h i k : ℂ) * ((z + k) ^ (i + j + 1))⁻¹) * hc'

theorem Dc_hasDerivAt_real (n : ℕ) (h : Fin 6 → ℤ) (j : ℕ) {x : ℝ} (hx : 0 < x) :
    HasDerivAt (fun y : ℝ => Dc n h j y) (((j : ℂ) + 1) * Dc n h (j + 1) x) x := by
  refine (Dc_hasDerivAt n h j fun k _ => ?_).comp_ofReal
  intro h0
  have := congrArg Complex.re h0
  simp at this
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem Pc_differentiableAt (n : ℕ) (h : Fin 6 → ℤ) {z : ℂ} (hz : ∀ k ≤ n, z + k ≠ 0) :
    DifferentiableAt ℂ (Pc n h) z := by
  have := (Dc_hasDerivAt n h 0 hz).differentiableAt
  have he : Pc n h = Dc n h 0 := funext fun t => Pc_eq_Dc_zero n h t
  rw [he]; exact this

theorem add_nat_ne_zero_of_re_pos {z : ℂ} (hz : 0 < z.re) (k : ℕ) : z + k ≠ 0 := by
  intro h0
  have := congrArg Complex.re h0
  simp at this
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

theorem add_nat_ne_zero_of_im_pos {z : ℂ} (hz : 0 < z.im) (k : ℕ) : z + k ≠ 0 := by
  intro h0
  have := congrArg Complex.im h0
  simp at this
  linarith

theorem Pc_differentiableOn_re (n : ℕ) (h : Fin 6 → ℤ) :
    DifferentiableOn ℂ (Pc n h) {t | 0 < t.re} := fun _ ht =>
  (Pc_differentiableAt n h fun k _ => add_nat_ne_zero_of_re_pos ht k).differentiableWithinAt

theorem Pc_differentiableOn_im (n : ℕ) (h : Fin 6 → ℤ) :
    DifferentiableOn ℂ (Pc n h) {t | 0 < t.im} := fun _ ht =>
  (Pc_differentiableAt n h fun k _ => add_nat_ne_zero_of_im_pos ht k).differentiableWithinAt

/-- Conjugation symmetry of `Pc`. -/
theorem Pc_conj (n : ℕ) (h : Fin 6 → ℤ) (t : ℂ) :
    Pc n h ((starRingEnd ℂ) t) = (starRingEnd ℂ) (Pc n h t) := by
  unfold Pc
  simp only [map_sum, map_mul, map_inv₀, map_pow, map_add, map_natCast, map_ratCast]

/-- `R_n = ∑ r_{i,k} (t+k)^{-i}` off the poles (from `Stmt_PF.poly`). -/
theorem Pc_eq_Rc (hPF : Stmt_PF) {n : ℕ} {h : Fin 6 → ℤ} (hh : Admissible n h) {t : ℂ}
    (ht : ∀ j ≤ n, t + j ≠ 0) : Pc n h t = Rc n h t := by
  have hpoly := congrArg (Polynomial.aeval t) (hPF.poly n h hh)
  simp only [Rnum, PFpoly, map_mul, map_add, map_sum, map_prod, map_pow, Polynomial.aeval_X,
    Polynomial.aeval_C, eq_ratCast] at hpoly
  push_cast at hpoly
  have hD : (∏ j ∈ range (n + 1), (t + j)) ≠ 0 := by
    rw [Finset.prod_ne_zero_iff]
    intro j hj
    exact ht j (by simpa [Nat.lt_succ_iff] using hj)
  unfold Rc
  rw [eq_div_iff (pow_ne_zero 6 hD)]
  have hnum : (2 * t + n) * ∏ p : Fin 6, ∏ u ∈ offsets n (h p), (t + 1 / 2 + u) =
      (2 * t + n) * ∏ p : Fin 6, ∏ u ∈ offsets n (h p), (t + (1 / 2 + u)) := by
    simp only [add_assoc]
  rw [hnum, hpoly]
  unfold Pc
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hi6 : i ≤ 6 := (Finset.mem_Icc.1 hi).2
  have htk : t + k ≠ 0 := ht k (by simpa [Nat.lt_succ_iff] using hk)
  rw [← Finset.prod_pow, ← Finset.prod_erase_mul _ _ hk]
  have hsplit : (t + (k : ℂ)) ^ 6 = (t + k) ^ (6 - i) * (t + k) ^ i := by
    rw [← pow_add]; congr 1; omega
  rw [hsplit]
  field_simp

/-! ### Bounds on `Pc` -/

/-- `∑_{i,k} |r_{i,k}|`. -/
def MP (n : ℕ) (h : Fin 6 → ℤ) : ℝ :=
  ∑ i ∈ Icc 1 6, ∑ k ∈ range (n + 1), ‖(rcoef n h i k : ℂ)‖

/-- `∑_{i,k} |r_{i,k}| (1 + k)`. -/
def M2 (n : ℕ) (h : Fin 6 → ℤ) : ℝ :=
  ∑ i ∈ Icc 1 6, ∑ k ∈ range (n + 1), ‖(rcoef n h i k : ℂ)‖ * (1 + k)

theorem MP_nonneg (n : ℕ) (h : Fin 6 → ℤ) : 0 ≤ MP n h :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem M2_nonneg (n : ℕ) (h : Fin 6 → ℤ) : 0 ≤ M2 n h :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => by positivity

theorem norm_Pc_le (n : ℕ) (h : Fin 6 → ℤ) {t : ℂ} (ht : ∀ k ≤ n, 1 ≤ ‖t + k‖) :
    ‖Pc n h t‖ ≤ MP n h := by
  unfold Pc MP
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k hk => ?_)
  have h1 := ht k (by simpa [Nat.lt_succ_iff] using hk)
  rw [norm_mul, norm_inv, norm_pow]
  have : (‖t + k‖ ^ i)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ h1)
  calc ‖(rcoef n h i k : ℂ)‖ * (‖t + k‖ ^ i)⁻¹ ≤ ‖(rcoef n h i k : ℂ)‖ * 1 := by gcongr
    _ = ‖(rcoef n h i k : ℂ)‖ := mul_one _

theorem norm_le_norm_add_nat {t : ℂ} (ht : 0 ≤ t.re) (k : ℕ) : ‖t‖ ≤ ‖t + k‖ := by
  have h1 : ‖t‖ ^ 2 ≤ ‖t + k‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.natCast_re, Complex.add_im, Complex.natCast_im, add_zero]
    have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith
  exact le_of_sq_le_sq (by simpa using h1) (norm_nonneg _) |>.trans_eq' rfl |> fun h => by
    nlinarith [norm_nonneg t, norm_nonneg (t + k), sq_nonneg (‖t‖ - ‖t + k‖)]

/-- With `c₁ = 0`: `‖R_n(t)‖ ≤ M₂ / ‖t‖²` for `Re t ≥ 0`, `‖t‖ ≥ 1`. -/
theorem norm_Pc_le_sq (hV : Stmt_CoeffVanish) {n : ℕ} {h : Fin 6 → ℤ} (hh : Admissible n h)
    {t : ℂ} (hre : 0 ≤ t.re) (ht1 : 1 ≤ ‖t‖) : ‖Pc n h t‖ ≤ M2 n h / ‖t‖ ^ 2 := by
  have hc1 : ∑ k ∈ range (n + 1), (rcoef n h 1 k : ℂ) = 0 := by
    have := hV.c1 n h hh
    unfold csum genCsum at this
    exact_mod_cast this
  have htpos : 0 < ‖t‖ := by linarith
  have ht0 : t ≠ 0 := norm_pos_iff.mp htpos
  have hdecomp : Pc n h t = ∑ i ∈ Icc 1 6, ∑ k ∈ range (n + 1),
      (rcoef n h i k : ℂ) * (((t + k) ^ i)⁻¹ - if i = 1 then t⁻¹ else 0) := by
    have hzero : ∑ i ∈ Icc 1 6, ∑ k ∈ range (n + 1),
        (rcoef n h i k : ℂ) * (if i = 1 then t⁻¹ else 0) = 0 := by
      have : ∀ i ∈ Finset.Icc 1 6, ∑ k ∈ range (n + 1),
          (rcoef n h i k : ℂ) * (if i = 1 then t⁻¹ else 0) =
            if i = 1 then (∑ k ∈ range (n + 1), (rcoef n h 1 k : ℂ)) * t⁻¹ else 0 := by
        intro i _
        split_ifs with hi
        · subst hi; rw [Finset.sum_mul]
        · simp
      rw [Finset.sum_congr rfl this, Finset.sum_ite_eq' (Finset.Icc 1 6) 1, hc1]
      simp
    calc Pc n h t = Pc n h t - 0 := (sub_zero _).symm
      _ = Pc n h t - ∑ i ∈ Icc 1 6, ∑ k ∈ range (n + 1),
            (rcoef n h i k : ℂ) * (if i = 1 then t⁻¹ else 0) := by rw [hzero]
      _ = _ := by
          unfold Pc
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k _ => ?_
          ring
  rw [hdecomp]
  unfold M2
  rw [Finset.sum_div]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun i hi => ?_)
  rw [Finset.sum_div]
  refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun k _ => ?_)
  have hi1 : 1 ≤ i := (Finset.mem_Icc.1 hi).1
  have htk : ‖t‖ ≤ ‖t + k‖ := norm_le_norm_add_nat hre k
  have htk0 : t + k ≠ 0 := norm_pos_iff.mp (lt_of_lt_of_le htpos htk)
  rw [norm_mul, mul_div_assoc]
  gcongr
  split_ifs with h1
  · subst h1
    rw [pow_one]
    have : (t + k)⁻¹ - t⁻¹ = -(k : ℂ) * (t⁻¹ * (t + k)⁻¹) := by field_simp; ring
    rw [this, norm_mul, norm_mul, norm_neg, Complex.norm_natCast, norm_inv, norm_inv]
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    calc (k : ℝ) * (‖t‖⁻¹ * ‖t + ↑k‖⁻¹) ≤ (1 + k) * (‖t‖⁻¹ * ‖t‖⁻¹) := by
          gcongr
          linarith
      _ = (1 + k) / ‖t‖ ^ 2 := by field_simp
  · rw [sub_zero, norm_inv, norm_pow]
    have hi2 : 2 ≤ i := by omega
    have htk1 : 1 ≤ ‖t + k‖ := le_trans ht1 htk
    calc (‖t + ↑k‖ ^ i)⁻¹ ≤ (‖t + ↑k‖ ^ 2)⁻¹ := by
          gcongr
      _ ≤ (‖t‖ ^ 2)⁻¹ := by gcongr
      _ ≤ (1 + k) / ‖t‖ ^ 2 := by
          rw [inv_eq_one_div]
          gcongr
          have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
          linarith

/-! ### Taylor coefficients at the critical half-integers -/

theorem inv_C_add_X_pow_succ (c : ℚ) (hc : c ≠ 0) (d : ℕ) :
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

theorem coeff_inv_C_add_X_pow (c : ℚ) (hc : c ≠ 0) (i j : ℕ) (hi : 1 ≤ i) :
    coeff j ((C c + X : PowerSeries ℚ) ^ i)⁻¹ = acoef i j * (c ^ (i + j))⁻¹ := by
  obtain ⟨d, rfl⟩ : ∃ d, i = d + 1 := ⟨i - 1, by omega⟩
  rw [inv_C_add_X_pow_succ c hc d, coeff_C_mul, coeff_rescale, coeff_mk]
  unfold acoef
  have hch : (d + j).choose d = (d + 1 + j - 1).choose j := by
    rw [show d + 1 + j - 1 = d + j by omega]
    exact Nat.choose_symm_add
  rw [hch, neg_pow, ← inv_pow]
  ring

theorem hpt_eq_ratCast (ν : ℤ) : hpt ν = (((ν : ℚ) + 1 / 2 : ℚ) : ℂ) := by
  simp only [hpt]; push_cast; ring

theorem half_int_add_nat_ne_zero (ν : ℤ) (k : ℕ) : ((ν : ℚ) + 1 / 2) + k ≠ 0 := by
  intro h0
  have h1 : ((2 * (ν + k) + 1 : ℤ) : ℚ) = 0 := by push_cast; linarith
  have h2 : (2 * (ν + k) + 1 : ℤ) = 0 := by exact_mod_cast h1
  omega

theorem hE_pos_succ (q : Fin 5) : 1 ≤ hE q.succ := by
  fin_cases q <;> simp [hE]

/-- `X⁵ ∣ numSer` at the critical half-integers of configuration E. -/
theorem X_pow_five_dvd_numSer (m : ℕ) (ν : ℤ) (hν1 : -(40 * (m : ℤ)) - m ≤ ν)
    (hν2 : ν ≤ (m : ℤ) - 1) :
    (X : PowerSeries ℚ) ^ 5 ∣ numSer (40 * m) (fun p => (m : ℤ) * hE p) ((ν : ℚ) + 1 / 2) := by
  unfold numSer
  rw [Fin.prod_univ_succ]
  refine Dvd.dvd.mul_left ?_ _
  have hX5 : (X : PowerSeries ℚ) ^ 5 = ∏ _q : Fin 5, (X : PowerSeries ℚ) := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hX5]
  refine Finset.prod_dvd_prod_of_dvd _ _ fun q _ => ?_
  have hq := hE_pos_succ q
  set u₀ : ℤ := -ν - 1
  have hu₀ : u₀ ∈ offsets (40 * m) ((m : ℤ) * hE q.succ) := by
    unfold offsets
    rw [Finset.mem_Ico]
    have : (m : ℤ) ≤ (m : ℤ) * hE q.succ := by
      have : (0 : ℤ) ≤ m := Int.natCast_nonneg m
      nlinarith
    push_cast
    constructor <;> omega
  have hval : (C ((ν : ℚ) + 1 / 2 + 1 / 2 + (u₀ : ℚ)) + X : PowerSeries ℚ) = X := by
    have : (ν : ℚ) + 1 / 2 + 1 / 2 + (u₀ : ℚ) = 0 := by
      simp only [u₀]; push_cast; ring
    rw [this, map_zero, zero_add]
  have := Finset.dvd_prod_of_mem
    (fun u : ℤ => (C ((ν : ℚ) + 1 / 2 + 1 / 2 + (u : ℚ)) + X : PowerSeries ℚ)) hu₀
  rw [hval] at this
  exact this

/-- **Critical zeros**: `D_j(ν + 1/2) = 0` for `j ≤ 4` and `-n - n/40 ≤ ν ≤ n/40 - 1`. -/
theorem Dc_hpt_eq_zero (hPF : Stmt_PF) (m : ℕ) (ν : ℤ) (hν1 : -(40 * (m : ℤ)) - m ≤ ν)
    (hν2 : ν ≤ (m : ℤ) - 1) (j : ℕ) (hj : j ≤ 4) :
    Dc (40 * m) (fun p => (m : ℤ) * hE p) j (hpt ν) = 0 := by
  set N := 40 * m
  set hh : Fin 6 → ℤ := fun p => (m : ℤ) * hE p
  set y : ℚ := (ν : ℚ) + 1 / 2
  have hy : ∀ j ≤ N, y + (j : ℚ) ≠ 0 := fun j _ => half_int_add_nat_ne_zero ν j
  have hser := hPF.series N hh y (admissible_E m) hy
  have hL : coeff j (Rser N hh y) = 0 := by
    obtain ⟨F, hF⟩ := X_pow_five_dvd_numSer m ν hν1 hν2
    have hR : Rser N hh y = X ^ 5 * ((C (2 * y + N) + C 2 * X) * F *
        ((∏ j ∈ range (N + 1), (C (y + j) + X)) ^ 6)⁻¹) := by
      unfold Rser
      rw [hF]
      ring
    rw [hR, PowerSeries.coeff_X_pow_mul']
    rw [ite_eq_right_iff.mpr (fun h => absurd h (by omega))]
  have hRHS : coeff j (∑ i ∈ Icc 1 6, ∑ k ∈ range (N + 1),
      C (rcoef N hh i k) * ((C (y + k) + X) ^ i)⁻¹) =
        ∑ i ∈ Icc 1 6, ∑ k ∈ range (N + 1),
          rcoef N hh i k * (acoef i j * ((y + k) ^ (i + j))⁻¹) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [coeff_C_mul, coeff_inv_C_add_X_pow _ (half_int_add_nat_ne_zero ν k) i j
      (Finset.mem_Icc.1 hi).1]
  rw [hser, hRHS] at hL
  have hcast := congrArg (fun q : ℚ => (q : ℂ)) hL
  simp only [Rat.cast_sum, Rat.cast_mul, Rat.cast_inv, Rat.cast_pow, Rat.cast_add,
    Rat.cast_natCast, Rat.cast_zero] at hcast
  unfold Dc
  rw [hpt_eq_ratCast]
  rw [← hcast]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  simp only [y]
  push_cast
  ring

/-- **Reflection symmetry** `D_j(-n-z) = (-1)^{j+1} D_j(z)`. -/
theorem Dc_symm (hV : Stmt_CoeffVanish) {n : ℕ} {h : Fin 6 → ℤ} (hh : Admissible n h) (j : ℕ)
    (z : ℂ) : Dc n h j (-(n : ℂ) - z) = (-1) ^ (j + 1) * Dc n h j z := by
  unfold Dc
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  have hk' : k ≤ n := by simpa [Nat.lt_succ_iff] using hk
  have hnk : n + 1 - 1 - k = n - k := by omega
  rw [hnk, hV.symm n h hh i k hk']
  have hcast : (((n - k : ℕ)) : ℂ) = (n : ℂ) - k := by push_cast [Nat.cast_sub hk']; ring
  rw [hcast]
  have hneg : -(n : ℂ) - z + ((n : ℂ) - k) = -(z + k) := by ring
  rw [hneg]
  have e1 : ((-(z + (k : ℂ))) ^ (i + j))⁻¹ = (-1) ^ (i + j) * ((z + k) ^ (i + j))⁻¹ := by
    rw [neg_pow (z + (k : ℂ)), mul_inv, ← inv_pow, inv_neg, inv_one]
  rw [e1]
  push_cast
  have h2 : ((-1 : ℂ) ^ (i + 1)) * (-1) ^ (i + j) = (-1) ^ (j + 1) := by
    rw [← pow_add]
    have : i + 1 + (i + j) = (j + 1) + 2 * i := by ring
    rw [this, pow_add, pow_mul]
    norm_num
  linear_combination ((rcoef n h i k : ℂ) * (acoef i j : ℂ) * ((z + k) ^ (i + j))⁻¹) * h2

/-! ### Sums over the half-integers -/

theorem summable_inv_hpt_add_pow (a : ℂ) {s : ℕ} (hs : 2 ≤ s) :
    Summable fun ν : ℤ => ((hpt ν + a) ^ s)⁻¹ := by
  refine (summable_norm_inv_int_add_pow (1 / 2 + a) hs).of_norm.congr fun ν => ?_
  simp only [hpt]
  ring_nf

theorem summable_Dc_hpt (n : ℕ) (h : Fin 6 → ℤ) {j : ℕ} (hj : 1 ≤ j) :
    Summable fun ν : ℤ => Dc n h j (hpt ν) := by
  unfold Dc
  refine summable_sum fun i hi => summable_sum fun k _ => ?_
  have hi1 := (Finset.mem_Icc.1 hi).1
  exact (summable_inv_hpt_add_pow (k : ℂ) (by omega : 2 ≤ i + j)).mul_left _

/-- `Z_s = ∑_{ν ∈ ℤ} (ν + 1/2)^{-s}`. -/
def Zc (s : ℕ) : ℂ := ∑' ν : ℤ, ((hpt ν) ^ s)⁻¹

/-- `Z⁺_s = ∑_{l ≥ 0} (l + 1/2)^{-s}`. -/
def Zp (s : ℕ) : ℂ := ∑' l : ℕ, ((hpt l) ^ s)⁻¹

theorem tsum_inv_hpt_add_nat_pow (N : ℕ) (k : ℕ) :
    ∑' ν : ℤ, ((hpt ν + k) ^ N)⁻¹ = Zc N := by
  unfold Zc
  have := (Equiv.addRight (k : ℤ)).tsum_eq (fun ν => ((hpt ν) ^ N)⁻¹)
  rw [← this]
  congr 1
  ext ν
  simp only [Equiv.coe_addRight, hpt]
  push_cast
  ring_nf

/-- **Sum over all half-integers**: `∑_ν D_j(ν+1/2) = ∑_i a(i,j) c_i Z_{i+j}`. -/
theorem tsum_Dc_hpt (n : ℕ) (h : Fin 6 → ℤ) {j : ℕ} (hj : 1 ≤ j) :
    ∑' ν : ℤ, Dc n h j (hpt ν) =
      ∑ i ∈ Icc 1 6, (acoef i j : ℂ) * (csum n h i : ℂ) * Zc (i + j) := by
  unfold Dc
  have hs1 : ∀ i ∈ Finset.Icc 1 6, Summable fun ν : ℤ => ∑ k ∈ range (n + 1),
      (rcoef n h i k : ℂ) * (acoef i j : ℂ) * ((hpt ν + k) ^ (i + j))⁻¹ := fun i hi =>
    summable_sum fun k _ =>
      (summable_inv_hpt_add_pow (k : ℂ) (by have := (Finset.mem_Icc.1 hi).1; omega)).mul_left _
  rw [Summable.tsum_finsetSum hs1]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hs2 : ∀ k ∈ range (n + 1), Summable fun ν : ℤ =>
      (rcoef n h i k : ℂ) * (acoef i j : ℂ) * ((hpt ν + k) ^ (i + j))⁻¹ := fun k _ =>
    (summable_inv_hpt_add_pow (k : ℂ) (by have := (Finset.mem_Icc.1 hi).1; omega)).mul_left _
  rw [Summable.tsum_finsetSum hs2]
  simp_rw [tsum_mul_left, tsum_inv_hpt_add_nat_pow]
  unfold csum genCsum
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem tsum_nat_shift_zero {f : ℕ → ℂ} (hf : Summable f) (M : ℕ) (hz : ∀ l < M, f l = 0) :
    ∑' l : ℕ, f l = ∑' l : ℕ, f (l + M) := by
  rw [← hf.sum_add_tsum_nat_add M, Finset.sum_eq_zero fun l hl => hz l (Finset.mem_range.1 hl),
    zero_add]

/-- For odd `j ∈ {1, 3}`, the two-sided sum is twice the sum to the right of `c = n/40`. -/
theorem tsum_Dc_hpt_eq_two_mul (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (m : ℕ) {j : ℕ}
    (hj : j = 1 ∨ j = 3) :
    ∑' ν : ℤ, Dc (40 * m) (fun p => (m : ℤ) * hE p) j (hpt ν) =
      2 * ∑' l : ℕ, Dc (40 * m) (fun p => (m : ℤ) * hE p) j (hpt ((m : ℤ) + l)) := by
  set N := 40 * m
  set hh : Fin 6 → ℤ := fun p => (m : ℤ) * hE p
  have hj1 : 1 ≤ j := by rcases hj with rfl | rfl <;> norm_num
  have hj4 : j ≤ 4 := by rcases hj with rfl | rfl <;> norm_num
  set f : ℤ → ℂ := fun ν => Dc N hh j (hpt ν) with hf
  have hS : Summable f := summable_Dc_hpt N hh hj1
  have hinj1 : Function.Injective (fun l : ℕ => (l : ℤ)) := Nat.cast_injective
  have hinj2 : Function.Injective (fun l : ℕ => -((l : ℤ) + 1)) := by
    intro a b hab; simp only [neg_inj, add_left_inj, Nat.cast_inj] at hab; exact hab
  have hinj3 : Function.Injective (fun l : ℕ => (l : ℤ) - N) := by
    intro a b hab; simp only [sub_left_inj, Nat.cast_inj] at hab; exact hab
  have hS1 : Summable fun l : ℕ => f l := hS.comp_injective hinj1
  have hS2 : Summable fun l : ℕ => f (-((l : ℤ) + 1)) := hS.comp_injective hinj2
  have hS3 : Summable fun l : ℕ => f ((l : ℤ) - N) := hS.comp_injective hinj3
  rw [tsum_of_nat_of_neg_add_one hS1 hS2]
  -- the right part
  have hR : ∑' l : ℕ, f l = ∑' l : ℕ, f ((m : ℤ) + l) := by
    rw [tsum_nat_shift_zero hS1 m fun l hl => ?_]
    · congr 1; ext l; push_cast; ring_nf
    · exact Dc_hpt_eq_zero hPF m l (by omega) (by omega) j hj4
  -- the left part, by symmetry
  have hsymm : ∀ l : ℕ, f (-((l : ℤ) + 1)) = f ((l : ℤ) - N) := by
    intro l
    simp only [hf]
    have hpt_eq : hpt (-((l : ℤ) + 1)) = -(N : ℂ) - hpt ((l : ℤ) - N) := by
      simp only [hpt]; push_cast; ring
    rw [hpt_eq, Dc_symm hV (admissible_E m) j]
    rcases hj with rfl | rfl <;> norm_num <;> rfl
  have hL : ∑' l : ℕ, f (-((l : ℤ) + 1)) = ∑' l : ℕ, f ((m : ℤ) + l) := by
    simp_rw [hsymm]
    rw [tsum_nat_shift_zero hS3 (N + m) fun l hl => ?_]
    · congr 1; ext l; push_cast; ring_nf
    · exact Dc_hpt_eq_zero hPF m _ (by omega) (by omega) j hj4
  rw [hR, hL]
  ring

/-- `∑_{l ≥ 0} (l + k + 1/2)^{-s} = Z⁺_s - A_k^{(s)}`. -/
theorem tsum_inv_hpt_nat_add (s k : ℕ) (hs : 2 ≤ s) :
    ∑' l : ℕ, ((hpt l + k) ^ s)⁻¹ = Zp s - (Ahalf k s : ℂ) := by
  have hsum : Summable fun l : ℕ => ((hpt l) ^ s)⁻¹ := by
    have := (summable_inv_hpt_add_pow 0 hs).comp_injective
      (Nat.cast_injective (R := ℤ))
    simpa [Function.comp_def] using this
  unfold Zp
  rw [← hsum.sum_add_tsum_nat_add k]
  have h1 : ∑' l : ℕ, ((hpt l + k) ^ s)⁻¹ = ∑' l : ℕ, ((hpt ((l + k : ℕ) : ℤ)) ^ s)⁻¹ := by
    congr 1; ext l; simp only [hpt]; push_cast; ring_nf
  have h2 : (Ahalf k s : ℂ) = ∑ l ∈ range k, ((hpt l) ^ s)⁻¹ := by
    unfold Ahalf
    push_cast
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [hpt]; push_cast
    rw [inv_pow]
  rw [h1, h2]
  ring

theorem acoef_four (i : ℕ) (hi : i ∈ Finset.Icc 1 6) :
    (acoef i 4 : ℚ) = (i : ℚ) * (i + 1) * (i + 2) * (i + 3) / 24 := by
  rw [Finset.mem_Icc] at hi
  obtain ⟨h1, h2⟩ := hi
  interval_cases i <;> simp [acoef, Nat.choose] <;> norm_num

/-- The one-sided sum for `j = 4`: `∑_{l≥0} D_4(m + l + 1/2) = ∑_i a(i,4) c_i Z⁺_{i+4} + ρ₀/24`. -/
theorem tsum_Dc4 (hPF : Stmt_PF) (m : ℕ) :
    ∑' l : ℕ, Dc (40 * m) (fun p => (m : ℤ) * hE p) 4 (hpt ((m : ℤ) + l)) =
      ∑ i ∈ Icc 1 6, (acoef i 4 : ℂ) * (csum (40 * m) (fun p => (m : ℤ) * hE p) i : ℂ) *
        Zp (i + 4) + (rho0 (40 * m) (fun p => (m : ℤ) * hE p) : ℂ) / 24 := by
  set N := 40 * m
  set hh : Fin 6 → ℤ := fun p => (m : ℤ) * hE p
  have hS : Summable fun l : ℕ => Dc N hh 4 (hpt l) :=
    (summable_Dc_hpt N hh (by norm_num : 1 ≤ 4)).comp_injective (Nat.cast_injective (R := ℤ))
  have hshift : ∑' l : ℕ, Dc N hh 4 (hpt ((m : ℤ) + l)) = ∑' l : ℕ, Dc N hh 4 (hpt l) := by
    rw [tsum_nat_shift_zero hS m fun l hl => ?_]
    · congr 1; ext l; push_cast; ring_nf
    · exact Dc_hpt_eq_zero hPF m l (by omega) (by omega) 4 le_rfl
  rw [hshift]
  unfold Dc
  have hs1 : ∀ i ∈ Finset.Icc 1 6, Summable fun l : ℕ => ∑ k ∈ range (N + 1),
      (rcoef N hh i k : ℂ) * (acoef i 4 : ℂ) * ((hpt (l : ℤ) + k) ^ (i + 4))⁻¹ := by
    intro i hi
    refine summable_sum fun k _ => ?_
    have h1 := (summable_inv_hpt_add_pow (k : ℂ)
      (by have := (Finset.mem_Icc.1 hi).1; omega : 2 ≤ i + 4)).comp_injective
        (Nat.cast_injective (R := ℤ))
    exact (h1.mul_left ((rcoef N hh i k : ℂ) * (acoef i 4 : ℂ))).congr fun l => rfl
  rw [Summable.tsum_finsetSum hs1]
  have hrho : (rho0 N hh : ℂ) / 24 = -∑ i ∈ Icc 1 6, ∑ k ∈ range (N + 1),
      (rcoef N hh i k : ℂ) * (acoef i 4 : ℂ) * (Ahalf k (i + 4) : ℂ) := by
    unfold rho0 genRho0
    push_cast
    rw [neg_div, Finset.sum_div]
    congr 1
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun k _ => ?_
    have := acoef_four i hi
    have h' : (acoef i 4 : ℂ) = (i : ℂ) * (i + 1) * (i + 2) * (i + 3) / 24 := by
      rw [this]; push_cast; ring
    rw [h']
    ring
  rw [hrho, ← sub_eq_add_neg, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i hi => ?_
  have hi1 := (Finset.mem_Icc.1 hi).1
  have hs2 : ∀ k ∈ range (N + 1), Summable fun l : ℕ =>
      (rcoef N hh i k : ℂ) * (acoef i 4 : ℂ) * ((hpt (l : ℤ) + k) ^ (i + 4))⁻¹ := by
    intro k _
    have h1 := (summable_inv_hpt_add_pow (k : ℂ) (by omega : 2 ≤ i + 4)).comp_injective
      (Nat.cast_injective (R := ℤ))
    exact (h1.mul_left ((rcoef N hh i k : ℂ) * (acoef i 4 : ℂ))).congr fun l => rfl
  rw [Summable.tsum_finsetSum hs2]
  simp_rw [tsum_mul_left]
  have hk : ∀ k : ℕ, ∑' l : ℕ, ((hpt (l : ℤ) + k) ^ (i + 4))⁻¹ = Zp (i + 4) - (Ahalf k (i + 4) : ℂ) :=
    fun k => tsum_inv_hpt_nat_add (i + 4) k (by omega)
  simp_rw [hk]
  unfold csum genCsum
  push_cast
  rw [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

-- (part: growth_pw)

/-! ## The primitive `Gf` -/

/-- A primitive of `σ ↦ log(σ² + y²)/2` (for `y > 0`); at `y = 0` it is `a log|a| - a`. -/
def Gf (a y : ℝ) : ℝ := a / 2 * Real.log (a ^ 2 + y ^ 2) + y * Real.arctan (a / y) - a

theorem Gf_hasDerivAt {y : ℝ} (hy : 0 < y) (a : ℝ) :
    HasDerivAt (fun a => Gf a y) (Real.log (a ^ 2 + y ^ 2) / 2) a := by
  have hpos : 0 < a ^ 2 + y ^ 2 := by positivity
  have h1 : HasDerivAt (fun a : ℝ => a ^ 2 + y ^ 2) (2 * a) a := by
    simpa using (hasDerivAt_pow 2 a).add_const (y ^ 2)
  have h2 := h1.log hpos.ne'
  have h3 : HasDerivAt (fun a : ℝ => a / y) (1 / y) a := by
    simpa using (hasDerivAt_id a).div_const y
  have h4 := h3.arctan
  have h5 := ((hasDerivAt_id a).div_const 2).mul h2
  have h6 := h4.const_mul y
  have h7 := (h5.add h6).sub (hasDerivAt_id a)
  convert h7 using 1
  · funext a; simp [Gf]
  · have hy0 : y ≠ 0 := hy.ne'
    simp only [id]
    field_simp
    ring

theorem Gf_sub_ge {y : ℝ} (hy : 0 < y) {α β : ℝ} (hab : α ≤ β) {L : ℝ}
    (hL : ∀ ξ ∈ Set.Icc α β, L ≤ Real.log (ξ ^ 2 + y ^ 2) / 2) :
    L * (β - α) ≤ Gf β y - Gf α y := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun a => Gf a y)
      (fun a => Real.log (a ^ 2 + y ^ 2) / 2) h
      (fun x _ => (Gf_hasDerivAt hy x).continuousAt.continuousWithinAt)
      (fun x _ => Gf_hasDerivAt hy x)
    have h1 := hL ξ ⟨hξ.1.le, hξ.2.le⟩
    rw [hξeq] at h1
    have hpos : 0 < β - α := by linarith
    rw [le_div_iff₀ hpos] at h1
    linarith

theorem Gf_sub_le {y : ℝ} (hy : 0 < y) {α β : ℝ} (hab : α ≤ β) {L : ℝ}
    (hL : ∀ ξ ∈ Set.Icc α β, Real.log (ξ ^ 2 + y ^ 2) / 2 ≤ L) :
    Gf β y - Gf α y ≤ L * (β - α) := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  · obtain ⟨ξ, hξ, hξeq⟩ := exists_hasDerivAt_eq_slope (fun a => Gf a y)
      (fun a => Real.log (a ^ 2 + y ^ 2) / 2) h
      (fun x _ => (Gf_hasDerivAt hy x).continuousAt.continuousWithinAt)
      (fun x _ => Gf_hasDerivAt hy x)
    have h1 := hL ξ ⟨hξ.1.le, hξ.2.le⟩
    rw [hξeq] at h1
    have hpos : 0 < β - α := by linarith
    rw [div_le_iff₀ hpos] at h1
    linarith

theorem Gf_mono {y : ℝ} (hy : 1 ≤ y) {α β : ℝ} (hab : α ≤ β) : Gf α y ≤ Gf β y := by
  have := Gf_sub_ge (y := y) (by linarith) hab (L := 0) fun ξ _ => by
    have h1 : 1 ≤ ξ ^ 2 + y ^ 2 := by nlinarith
    have := Real.log_nonneg h1
    linarith
  linarith

/-- **Window bound (numerator)**, `y ≥ 1`: `∑_{i<N} log((q+i)²+y²)/2 ≤ Gf(q+N) - Gf(q-1)`. -/
theorem num_sum_le {y : ℝ} (hy : 1 ≤ y) (q : ℝ) (N : ℕ) :
    ∑ i ∈ range N, Real.log ((q + i) ^ 2 + y ^ 2) / 2 ≤ Gf (q + N) y - Gf (q - 1) y := by
  have hy0 : 0 < y := by linarith
  have key : ∀ N : ℕ, ∑ i ∈ range N, Real.log ((q + i) ^ 2 + y ^ 2) / 2 ≤
      Gf (if q + N - 1 < 0 then q + N - 1 else q + N) y - Gf (q - 1) y := by
    intro N
    induction N with
    | zero =>
      simp only [range_zero, sum_empty, Nat.cast_zero, add_zero]
      split_ifs with h
      · simp
      · have := Gf_mono hy (show q - 1 ≤ q by linarith); linarith
    | succ N ih =>
      rw [sum_range_succ]
      have hc : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
      rw [hc]
      by_cases hN : q + N < 0
      · have h1 : q + ((N : ℝ) + 1) - 1 < 0 := by linarith
        have h2 : q + N - 1 < 0 := by linarith
        simp only [h1, ↓reduceIte]
        simp only [h2, ↓reduceIte] at ih
        have hinc := Gf_sub_ge hy0 (show q + N - 1 ≤ q + N by linarith)
          (L := Real.log ((q + N) ^ 2 + y ^ 2) / 2) fun ξ hξ => by
            have hsq : (q + N) ^ 2 + y ^ 2 ≤ ξ ^ 2 + y ^ 2 := by nlinarith [hξ.1, hξ.2]
            have := Real.log_le_log (by positivity) hsq
            linarith
        have he : q + ((N : ℝ) + 1) - 1 = q + N := by ring
        rw [he]
        nlinarith
      · push Not at hN
        have h1 : ¬ (q + ((N : ℝ) + 1) - 1 < 0) := by push Not; linarith
        simp only [h1, ↓reduceIte]
        have hle : (if q + N - 1 < 0 then q + N - 1 else q + N) ≤ q + N := by
          split_ifs <;> linarith
        have hmono := Gf_mono hy hle
        have hinc := Gf_sub_ge hy0 (show q + N ≤ q + (N + 1) by linarith)
          (L := Real.log ((q + N) ^ 2 + y ^ 2) / 2) fun ξ hξ => by
            have hsq : (q + N) ^ 2 + y ^ 2 ≤ ξ ^ 2 + y ^ 2 := by nlinarith [hξ.1, hξ.2]
            have := Real.log_le_log (by positivity) hsq
            linarith
        have he : q + ((N : ℝ) + 1) - (q + N) = 1 := by ring
        rw [he, mul_one] at hinc
        linarith
  have hle : (if q + N - 1 < 0 then q + N - 1 else q + N) ≤ q + N := by
    split_ifs <;> linarith
  have := Gf_mono hy hle
  linarith [key N]

/-- **Window bound (denominator)**, `y ≥ 1`, `x ≥ 0`. -/
theorem den_sum_ge {y : ℝ} (hy : 1 ≤ y) {x : ℝ} (hx : 0 ≤ x) (N : ℕ) :
    Gf (x + N) y - Gf x y ≤ ∑ j ∈ range (N + 1), Real.log ((x + j) ^ 2 + y ^ 2) / 2 := by
  have hy0 : 0 < y := by linarith
  induction N with
  | zero =>
    simp only [Nat.cast_zero, add_zero, sub_self, zero_add, sum_range_one]
    have h1 : 1 ≤ x ^ 2 + y ^ 2 := by nlinarith
    have := Real.log_nonneg h1
    linarith
  | succ N ih =>
    rw [sum_range_succ]
    have hc : ((N + 1 : ℕ) : ℝ) = (N : ℝ) + 1 := by push_cast; ring
    rw [hc]
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have hinc := Gf_sub_le hy0 (show x + N ≤ x + (N + 1) by linarith)
      (L := Real.log ((x + (N + 1)) ^ 2 + y ^ 2) / 2) fun ξ hξ => by
        have hsq : ξ ^ 2 + y ^ 2 ≤ (x + (N + 1)) ^ 2 + y ^ 2 := by nlinarith [hξ.1, hξ.2]
        have := Real.log_le_log (by nlinarith) hsq
        linarith
    have he : x + ((N : ℝ) + 1) - (x + N) = 1 := by ring
    rw [he, mul_one] at hinc
    linarith

/-- Reindexing an integer interval. -/
theorem sum_Ico_int_eq_sum_range (g : ℤ → ℝ) (a b : ℤ) (hab : a ≤ b) :
    ∑ u ∈ Finset.Ico a b, g u = ∑ i ∈ range (b - a).toNat, g (a + i) := by
  refine Finset.sum_nbij' (fun u => (u - a).toNat) (fun i => a + (i : ℤ)) ?_ ?_ ?_ ?_ ?_
  · intro u hu
    simp only [Finset.mem_Ico, Finset.mem_range, Finset.mem_coe] at hu ⊢
    omega
  · intro i hi
    simp only [Finset.mem_Ico, Finset.mem_range, Finset.mem_coe] at hi ⊢
    omega
  · intro u hu
    simp only [Finset.mem_Ico, Finset.mem_range, Finset.mem_coe] at hu
    omega
  · intro i _
    omega
  · intro u hu
    simp only [Finset.mem_Ico] at hu
    congr 1
    omega

theorem num_sum_le_Ico {y : ℝ} (hy : 1 ≤ y) (x : ℝ) (a b : ℤ) (hab : a ≤ b) :
    ∑ u ∈ Finset.Ico a b, Real.log ((x + u) ^ 2 + y ^ 2) / 2 ≤ Gf (x + b) y - Gf (x + a - 1) y := by
  rw [sum_Ico_int_eq_sum_range (fun u : ℤ => Real.log ((x + u) ^ 2 + y ^ 2) / 2) a b hab]
  have := num_sum_le hy (x + a) (b - a).toNat
  have hN : (((b - a).toNat : ℕ) : ℝ) = (b : ℝ) - a := by
    have : ((b - a).toNat : ℤ) = b - a := Int.toNat_of_nonneg (by omega)
    have h2 : (((b - a).toNat : ℤ) : ℝ) = ((b - a : ℤ) : ℝ) := by rw [this]
    push_cast at h2
    exact h2
  rw [hN] at this
  have e1 : x + a + (b - a) = x + b := by ring
  rw [e1] at this
  refine le_trans (le_of_eq ?_) this
  refine Finset.sum_congr rfl fun i _ => ?_
  push_cast
  ring_nf

/-- `‖w‖ = exp(log(re² + im²)/2)` when `Im w ≠ 0`. -/
theorem norm_eq_exp_log (w : ℂ) (hw : w.im ≠ 0) :
    ‖w‖ = Real.exp (Real.log (w.re ^ 2 + w.im ^ 2) / 2) := by
  have hpos : 0 < w.re ^ 2 + w.im ^ 2 := by
    have : 0 < w.im ^ 2 := by positivity
    linarith [sq_nonneg w.re]
  have h1 : ‖w‖ = Real.sqrt (w.re ^ 2 + w.im ^ 2) := Complex.norm_eq_sqrt_sq_add_sq w
  rw [h1, Real.sqrt_eq_rpow, Real.rpow_def_of_pos hpos]
  ring_nf

/-- **Product bound** (general admissible `(n, h)`, `Re t ≥ 0`, `Im t ≥ 1`). -/
theorem norm_Rc_le_exp {n : ℕ} {h : Fin 6 → ℤ} (hh : Admissible n h) {t : ℂ} (hre : 0 ≤ t.re)
    (him : 1 ≤ t.im) :
    ‖Rc n h t‖ ≤ ‖2 * t + (n : ℂ)‖ * Real.exp (∑ p : Fin 6,
      (Gf (t.re + 1 / 2 + ((n + h p : ℤ) : ℝ)) t.im - Gf (t.re + 1 / 2 + ((-h p : ℤ) : ℝ) - 1) t.im) -
        6 * (Gf (t.re + n) t.im - Gf t.re t.im)) := by
  set x := t.re with hx
  set y := t.im with hy
  have hy0 : 0 < y := by linarith
  have hfac : ∀ c : ℝ, ‖t + (c : ℂ)‖ = Real.exp (Real.log ((x + c) ^ 2 + y ^ 2) / 2) := by
    intro c
    have him' : (t + (c : ℂ)).im ≠ 0 := by simp; linarith
    rw [norm_eq_exp_log _ him']
    simp [x, y]
  have hnum : ∀ p : Fin 6, ∏ u ∈ offsets n (h p), ‖t + 1 / 2 + (u : ℂ)‖ ≤
      Real.exp (Gf (x + 1 / 2 + ((n + h p : ℤ) : ℝ)) y - Gf (x + 1 / 2 + ((-h p : ℤ) : ℝ) - 1) y) := by
    intro p
    have hadm := hh.2.1 p
    have hle : -h p ≤ (n : ℤ) + h p := by omega
    calc ∏ u ∈ offsets n (h p), ‖t + 1 / 2 + (u : ℂ)‖
        = ∏ u ∈ offsets n (h p), Real.exp (Real.log ((x + 1 / 2 + u) ^ 2 + y ^ 2) / 2) := by
          refine Finset.prod_congr rfl fun u _ => ?_
          have e1 : t + 1 / 2 + (u : ℂ) = t + (((1 / 2 : ℝ) + u : ℝ) : ℂ) := by push_cast; ring
          rw [e1, hfac]
          ring_nf
      _ = Real.exp (∑ u ∈ offsets n (h p), Real.log ((x + 1 / 2 + u) ^ 2 + y ^ 2) / 2) :=
          (Real.exp_sum _ _).symm
      _ ≤ _ := by
          apply Real.exp_le_exp.mpr
          unfold offsets
          exact num_sum_le_Ico him (x + 1 / 2) (-h p) (n + h p) hle
  have hden : Real.exp (Gf (x + n) y - Gf x y) ≤ ∏ j ∈ range (n + 1), ‖t + (j : ℂ)‖ := by
    calc Real.exp (Gf (x + n) y - Gf x y)
        ≤ Real.exp (∑ j ∈ range (n + 1), Real.log ((x + j) ^ 2 + y ^ 2) / 2) :=
          Real.exp_le_exp.mpr (den_sum_ge him hre n)
      _ = ∏ j ∈ range (n + 1), Real.exp (Real.log ((x + j) ^ 2 + y ^ 2) / 2) := Real.exp_sum _ _
      _ = ∏ j ∈ range (n + 1), ‖t + (j : ℂ)‖ := by
          refine Finset.prod_congr rfl fun j _ => ?_
          rw [show (j : ℂ) = ((j : ℝ) : ℂ) by push_cast; rfl, hfac]
  have hdpos : 0 < Real.exp (Gf (x + n) y - Gf x y) := Real.exp_pos _
  unfold Rc
  rw [norm_div, norm_mul, norm_pow, norm_prod, norm_prod]
  have hnum2 : ∏ p : Fin 6, ‖∏ u ∈ offsets n (h p), (t + 1 / 2 + (u : ℂ))‖ ≤
      ∏ p : Fin 6, Real.exp (Gf (x + 1 / 2 + ((n + h p : ℤ) : ℝ)) y -
        Gf (x + 1 / 2 + ((-h p : ℤ) : ℝ) - 1) y) := by
    refine Finset.prod_le_prod₀ (fun p _ => norm_nonneg _) fun p _ => ?_
    rw [norm_prod]
    exact hnum p
  have hden2 : Real.exp (Gf (x + n) y - Gf x y) ^ 6 ≤ (∏ j ∈ range (n + 1), ‖t + (j : ℂ)‖) ^ 6 :=
    pow_le_pow_left₀ hdpos.le hden 6
  calc ‖2 * t + (n : ℂ)‖ * (∏ p : Fin 6, ‖∏ u ∈ offsets n (h p), (t + 1 / 2 + (u : ℂ))‖) /
        (∏ j ∈ range (n + 1), ‖t + (j : ℂ)‖) ^ 6
      ≤ ‖2 * t + (n : ℂ)‖ * (∏ p : Fin 6, Real.exp (Gf (x + 1 / 2 + ((n + h p : ℤ) : ℝ)) y -
          Gf (x + 1 / 2 + ((-h p : ℤ) : ℝ) - 1) y)) / Real.exp (Gf (x + n) y - Gf x y) ^ 6 := by
        gcongr
      _ = _ := by
        rw [← Real.exp_sum, ← Real.exp_nat_mul, mul_div_assoc, ← Real.exp_sub]
        congr 2

/-- `η_p = hE_p / 40`. -/
def etaE (p : Fin 6) : ℝ := (hE p : ℝ) / 40

/-- **The landscape function** `Φ(τ) = ∑_p ∫_{-η_p}^{1+η_p} log|τ+σ| dσ - 6 ∫_0^1 log|τ+σ| dσ`
(`τ = x + iy`, `y > 0`), in closed form; `Φ(x, 0)` is the real profile. -/
def PhiE (x y : ℝ) : ℝ :=
  ∑ p : Fin 6, (Gf (x + 1 + etaE p) y - Gf (x - etaE p) y) - 6 * (Gf (x + 1) y - Gf x y)

theorem sum_etaE_six : etaE 0 + etaE 1 + etaE 2 + etaE 3 + etaE 4 + etaE 5 = 0 := by
  simp only [etaE, hE]
  norm_num

theorem Gf_scale {N : ℝ} (hN : 0 < N) (a : ℝ) {y : ℝ} (hy : 0 < y) :
    Gf (N * a) (N * y) = N * Gf a y + N * a * Real.log N := by
  unfold Gf
  have h1 : (N * a) ^ 2 + (N * y) ^ 2 = N ^ 2 * (a ^ 2 + y ^ 2) := by ring
  have h2 : 0 < a ^ 2 + y ^ 2 := by positivity
  rw [h1, Real.log_mul (by positivity) h2.ne', Real.log_pow, mul_div_mul_left _ _ hN.ne']
  push_cast
  ring

/-- Scaling of the window sums to the landscape function. -/
theorem window_scale {N : ℝ} (hN : 0 < N) (x : ℝ) {y : ℝ} (hy : 0 < y) :
    ∑ p : Fin 6, (Gf (x + N + N * etaE p) y - Gf (x - N * etaE p) y) -
      6 * (Gf (x + N) y - Gf x y) = N * PhiE (x / N) (y / N) := by
  have key : ∀ z : ℝ, Gf z y = N * Gf (z / N) (y / N) + z * Real.log N := by
    intro z
    have := Gf_scale hN (z / N) (y := y / N) (by positivity)
    rw [mul_div_cancel₀ _ hN.ne', mul_div_cancel₀ _ hN.ne'] at this
    rw [this]
  have h1 : ∀ p : Fin 6, (x + N + N * etaE p) / N = x / N + 1 + etaE p := by
    intro p; field_simp
  have h2 : ∀ p : Fin 6, (x - N * etaE p) / N = x / N - etaE p := by
    intro p; field_simp
  have h3 : (x + N) / N = x / N + 1 := by field_simp
  simp only [key, h1, h2, h3]
  unfold PhiE
  simp only [Fin.sum_univ_six]
  linear_combination (2 * N * Real.log N) * sum_etaE_six

theorem log_half_le {x y ξ B : ℝ} (hy : 1 ≤ y) (hB : 0 ≤ B) (hξ : |ξ| ≤ |x| + B) :
    Real.log (ξ ^ 2 + y ^ 2) / 2 ≤ Real.log (Real.sqrt (x ^ 2 + y ^ 2) + B) := by
  set r := Real.sqrt (x ^ 2 + y ^ 2) with hr
  have hr0 : 0 ≤ r := Real.sqrt_nonneg _
  have hr2 : r ^ 2 = x ^ 2 + y ^ 2 := Real.sq_sqrt (by positivity)
  have hxr : |x| ≤ r := by
    rw [hr]; exact Real.abs_le_sqrt (by nlinarith)
  have hpos : 0 < ξ ^ 2 + y ^ 2 := by nlinarith
  have hle : ξ ^ 2 + y ^ 2 ≤ (r + B) ^ 2 := by
    have h1 : ξ ^ 2 ≤ (|x| + B) ^ 2 := by
      rw [← sq_abs ξ]; exact pow_le_pow_left₀ (abs_nonneg _) hξ 2
    nlinarith [abs_nonneg x, sq_abs x, mul_le_mul_of_nonneg_right hxr hB]
  have hrB : 0 < r + B := by nlinarith
  calc Real.log (ξ ^ 2 + y ^ 2) / 2 ≤ Real.log ((r + B) ^ 2) / 2 := by
        gcongr
    _ = Real.log (r + B) := by rw [Real.log_pow]; push_cast; ring

/-- **Pointwise bound** for configuration E: for `Re t ≥ 0`, `Im t ≥ 1`,
`|R_n(t)| ≤ |2t + n| (|t| + 2n)^6 exp(n Φ(t/n))`, `n = 40 m`. -/
theorem norm_Rc_le (m : ℕ) (hm : 1 ≤ m) {t : ℂ} (hre : 0 ≤ t.re) (him : 1 ≤ t.im) :
    ‖Rc (40 * m) (fun p => (m : ℤ) * hE p) t‖ ≤
      ‖2 * t + ((40 * m : ℕ) : ℂ)‖ * ((‖t‖ + 80 * m) ^ 6 *
        Real.exp (40 * m * PhiE (t.re / (40 * m)) (t.im / (40 * m)))) := by
  set x := t.re with hx
  set y := t.im with hy
  have hy0 : 0 < y := by linarith
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN : (0 : ℝ) < 40 * m := by positivity
  have h1 := norm_Rc_le_exp (admissible_E m) hre him
  refine le_trans h1 ?_
  refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
  have htn : ‖t‖ = Real.sqrt (x ^ 2 + y ^ 2) := Complex.norm_eq_sqrt_sq_add_sq t
  set L := Real.log (‖t‖ + 80 * m) with hL
  have hL0 : 0 ≤ L := Real.log_nonneg (by nlinarith [norm_nonneg t])
  have hwin : ∀ ξ : ℝ, |ξ - x| ≤ 80 * m → Real.log (ξ ^ 2 + y ^ 2) / 2 ≤ L := by
    intro ξ hξ
    rw [hL, htn]
    refine log_half_le him (by positivity) ?_
    calc |ξ| = |x + (ξ - x)| := by ring_nf
      _ ≤ |x| + |ξ - x| := abs_add_le _ _
      _ ≤ |x| + 80 * m := by linarith
  have hhE : ∀ p : Fin 6, |(hE p : ℝ)| ≤ 17 := by
    intro p; fin_cases p <;> simp [hE] <;> norm_num
  have hbnd : ∀ p : Fin 6, -(17 * (m : ℝ)) ≤ m * hE p ∧ (m : ℝ) * hE p ≤ 17 * m := by
    intro p
    have hb := abs_le.mp (hhE p)
    have hm0 : (0 : ℝ) ≤ m := by positivity
    constructor <;> nlinarith [hb.1, hb.2]
  -- the two half-unit end pieces of each numerator window
  have hext1 : ∀ p : Fin 6, Gf (x + 1 / 2 + ((((40 * m : ℕ) : ℤ) + (m : ℤ) * hE p : ℤ) : ℝ)) y -
      Gf (x + 40 * m + m * hE p) y ≤ L / 2 := by
    intro p
    have e : x + 1 / 2 + ((((40 * m : ℕ) : ℤ) + (m : ℤ) * hE p : ℤ) : ℝ) =
        x + 40 * m + m * hE p + 1 / 2 := by push_cast; ring
    rw [e]
    have := Gf_sub_le hy0 (show x + 40 * m + m * hE p ≤ x + 40 * m + m * hE p + 1 / 2 by linarith)
      (L := L) fun ξ hξ => hwin ξ (by
        rw [abs_le]; have := hbnd p; constructor <;> nlinarith [hξ.1, hξ.2])
    have e2 : x + 40 * m + m * hE p + 1 / 2 - (x + 40 * m + m * hE p) = 1 / 2 := by ring
    rw [e2] at this
    linarith
  have hext2 : ∀ p : Fin 6, Gf (x - m * hE p) y -
      Gf (x + 1 / 2 + ((-((m : ℤ) * hE p) : ℤ) : ℝ) - 1) y ≤ L / 2 := by
    intro p
    have e : x + 1 / 2 + ((-((m : ℤ) * hE p) : ℤ) : ℝ) - 1 = x - m * hE p - 1 / 2 := by
      push_cast; ring
    rw [e]
    have := Gf_sub_le hy0 (show x - m * hE p - 1 / 2 ≤ x - m * hE p by linarith)
      (L := L) fun ξ hξ => hwin ξ (by
        rw [abs_le]; have := hbnd p; constructor <;> nlinarith [hξ.1, hξ.2])
    have e2 : x - m * hE p - (x - m * hE p - 1 / 2) = 1 / 2 := by ring
    rw [e2] at this
    linarith
  have hmain := window_scale hN x hy0
  have hetaE : ∀ p : Fin 6, (40 * (m : ℝ)) * etaE p = m * hE p := by
    intro p; unfold etaE; ring
  simp only [hetaE] at hmain
  have hsumext : ∑ p : Fin 6, (Gf (x + 1 / 2 + ((((40 * m : ℕ) : ℤ) + (m : ℤ) * hE p : ℤ) : ℝ)) y -
      Gf (x + 1 / 2 + ((-((m : ℤ) * hE p) : ℤ) : ℝ) - 1) y) ≤
      ∑ p : Fin 6, (Gf (x + 40 * m + m * hE p) y - Gf (x - m * hE p) y) + 6 * L := by
    have : ∀ p : Fin 6, Gf (x + 1 / 2 + ((((40 * m : ℕ) : ℤ) + (m : ℤ) * hE p : ℤ) : ℝ)) y -
        Gf (x + 1 / 2 + ((-((m : ℤ) * hE p) : ℤ) : ℝ) - 1) y ≤
        (Gf (x + 40 * m + m * hE p) y - Gf (x - m * hE p) y) + L := by
      intro p
      have := hext1 p
      have := hext2 p
      linarith
    calc _ ≤ ∑ p : Fin 6, ((Gf (x + 40 * m + m * hE p) y - Gf (x - m * hE p) y) + L) :=
          Finset.sum_le_sum fun p _ => this p
      _ = _ := by
          rw [Finset.sum_add_distrib]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          push_cast
          ring
  have hfin : (‖t‖ + 80 * m) ^ 6 = Real.exp (6 * L) := by
    rw [hL, show (6 : ℝ) * Real.log (‖t‖ + 80 * m) = ((6 : ℕ) : ℝ) * Real.log (‖t‖ + 80 * m) by
      norm_num, ← Real.log_pow, Real.exp_log (by positivity)]
  rw [hfin, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have e3 : (((40 * m : ℕ) : ℝ)) = 40 * m := by push_cast; ring
  have e4 : x + (((40 * m : ℕ) : ℝ)) = x + 40 * m := by rw [e3]
  rw [e4]
  linarith

-- (part: growth_rep)

/-! ## `Pc` along vertical lines -/

theorem Pc_vline_continuous (n : ℕ) (h : Fin 6 → ℤ) {c : ℝ} (hc : 0 < c) :
    Continuous fun y : ℝ => Pc n h (c + y * I) := by
  refine (Pc_differentiableOn_re n h).continuousOn.comp_continuous (continuous_vline c)
    fun y => ?_
  change 0 < ((c : ℂ) + (y : ℂ) * I).re
  rw [vline_re]; exact hc

theorem Pc_decay1 (hV : Stmt_CoeffVanish) {n : ℕ} {h : Fin 6 → ℤ} (hh : Admissible n h) :
    ∀ t : ℂ, 0 ≤ t.re → 1 ≤ ‖t‖ → ‖Pc n h t‖ ≤ M2 n h / ‖t‖ := by
  intro t ht0 ht1
  refine le_trans (norm_Pc_le_sq hV hh ht0 ht1) ?_
  have hpos : 0 < ‖t‖ := by linarith
  rw [div_le_div_iff₀ (by positivity) hpos]
  have := M2_nonneg n h
  rw [sq]
  exact mul_le_mul_of_nonneg_left (le_mul_of_one_le_left hpos.le ht1) this

theorem Pc_vline_integrable (hV : Stmt_CoeffVanish) {n : ℕ} {h : Fin 6 → ℤ}
    (hh : Admissible n h) {c : ℝ} (hc : 0 < c) :
    Integrable fun y : ℝ => Pc n h (c + y * I) := by
  have hcont := Pc_vline_continuous n h hc
  obtain ⟨K, hK⟩ := exists_bound_inv_one_add_sq hcont (le_refl 1) (M2_nonneg n h) fun y hy => by
    have h1 := abs_le_norm_vline c y
    have hn : 1 ≤ ‖(c : ℂ) + (y : ℂ) * I‖ := le_trans hy h1
    have := norm_Pc_le_sq hV hh (t := (c : ℂ) + (y : ℂ) * I) (by rw [vline_re]; exact hc.le) hn
    refine le_trans this ?_
    have hy0 : 0 < |y| := lt_of_lt_of_le one_pos hy
    rw [← sq_abs y]
    apply div_le_div_of_nonneg_left (M2_nonneg n h) (pow_pos hy0 2)
    exact pow_le_pow_left₀ (abs_nonneg _) h1 2
  exact integrable_of_bound_inv_one_add_sq hcont hK

/-- `∫ Pc(c+iy) (c+iy-x)^{-(j+1)} dy = -2π D_j(x)` for real `x > c > 0`. -/
theorem vline_Pc_right (hV : Stmt_CoeffVanish) {n : ℕ} {h : Fin 6 → ℤ} (hh : Admissible n h)
    {c : ℝ} (hc : 0 < c) (j : ℕ) {x : ℝ} (hx : c < x) :
    ∫ y : ℝ, Pc n h (c + y * I) * (((c : ℂ) + y * I - x) ^ (j + 1))⁻¹ =
      -2 * π * Dc n h j x :=
  vline_higher (c' := 0) hc (Pc_differentiableOn_re n h) (le_refl 1) (M2_nonneg n h)
    (fun t ht1 ht2 => Pc_decay1 hV hh t (le_trans hc.le ht1) ht2) (Pc_vline_integrable hV hh hc)
    (fun j x => Dc n h j x) (fun x _ => (Pc_eq_Dc_zero n h x).symm)
    (fun j x hx => Dc_hasDerivAt_real n h j (lt_trans hc hx)) j x hx

/-- Vanishing for poles to the left of the line. -/
theorem vline_Pc_left (hV : Stmt_CoeffVanish) {n : ℕ} {h : Fin 6 → ℤ} (hh : Admissible n h)
    {c : ℝ} (hc : 0 < c) {x : ℝ} (hx : x < c) {s : ℕ} (hs : 1 ≤ s) :
    ∫ y : ℝ, Pc n h (c + y * I) * (((c : ℂ) + y * I - x) ^ s)⁻¹ = 0 :=
  vline_left (c' := 0) hc (Pc_differentiableOn_re n h) (le_refl 1) (M2_nonneg n h)
    (fun t ht1 ht2 => Pc_decay1 hV hh t (le_trans hc.le ht1) ht2) hx hs

theorem summable_norm_hpt_sub (c : ℤ) {s : ℕ} (hs : 2 ≤ s) :
    Summable fun ν : ℤ => ‖((hpt (c - 1 - ν)) ^ s)⁻¹‖ := by
  have hsum0 : Summable fun ν : ℤ => ‖((hpt ν) ^ s)⁻¹‖ := by
    have := summable_norm_kerS_term 0 hs
    refine this.congr fun ν => ?_
    rw [norm_inv, norm_inv, norm_pow, norm_pow, zero_sub, norm_neg]
  have := (Equiv.summable_iff (Equiv.subLeft (c - 1))
    (f := fun ν : ℤ => ‖((hpt ν) ^ s)⁻¹‖)).mpr hsum0
  simpa only [Function.comp_def, Equiv.subLeft_apply] using this

theorem natCast_vline (c : ℕ) (y : ℝ) :
    (((c : ℝ) : ℂ) + (y : ℂ) * I) = (((c : ℤ) : ℂ) + (y : ℂ) * I) := by
  push_cast; rfl

/-- **Vertical-line representation**: `∫ Pc(c+iy) K_s(c+iy) dy = -2π ∑_{l ≥ 0} D_{s-1}(c+l+1/2)`
(`c ≥ 1` an integer, `s ≥ 2`). -/
theorem vline_Pc_kerS (hV : Stmt_CoeffVanish) {n : ℕ} {h : Fin 6 → ℤ} (hh : Admissible n h)
    (c : ℕ) (hc : 1 ≤ c) {s : ℕ} (hs : 2 ≤ s) :
    ∫ y : ℝ, Pc n h ((c : ℝ) + y * I) * kerS s ((c : ℝ) + y * I) =
      -2 * π * ∑' l : ℕ, Dc n h (s - 1) (hpt ((c : ℤ) + l)) := by
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  set G : ℤ → ℝ → ℂ := fun ν y =>
    Pc n h ((c : ℝ) + y * I) * ((((c : ℝ) : ℂ) + y * I - hpt ν) ^ s)⁻¹ with hG
  have hexp : ∀ y : ℝ, Pc n h ((c : ℝ) + y * I) * kerS s ((c : ℝ) + y * I) = ∑' ν : ℤ, G ν y := by
    intro y
    simp only [hG, kerS]
    rw [tsum_mul_left]
  have hker : ∀ (ν : ℤ) (y : ℝ), ‖((((c : ℝ) : ℂ) + y * I - hpt ν) ^ s)⁻¹‖ ≤
      ‖((hpt ((c : ℤ) - 1 - ν)) ^ s)⁻¹‖ := by
    intro ν y
    rw [norm_inv, norm_inv, norm_pow, norm_pow]
    have hpos : 0 < ‖hpt ((c : ℤ) - 1 - ν)‖ := lt_of_lt_of_le (by norm_num) (half_le_norm_hpt _)
    gcongr
    have := norm_sub_hpt_ge_of_int (c : ℤ) y ν
    rw [natCast_vline]
    exact this
  have hPint := Pc_vline_integrable hV hh hcpos
  have hne : ∀ (ν : ℤ) (y : ℝ), (((c : ℝ) : ℂ) + y * I - hpt ν) ≠ 0 := by
    intro ν y h0
    have h1 := hker ν y
    rw [h0, zero_pow (by omega), inv_zero, norm_zero] at h1
    have h2 : 0 < ‖((hpt ((c : ℤ) - 1 - ν)) ^ s)⁻¹‖ := by
      rw [norm_inv, norm_pow]
      have : 0 < ‖hpt ((c : ℤ) - 1 - ν)‖ := lt_of_lt_of_le (by norm_num) (half_le_norm_hpt _)
      positivity
    have h3 := norm_sub_hpt_ge_of_int (c : ℤ) y ν
    rw [← natCast_vline, h0, norm_zero] at h3
    have := half_le_norm_hpt ((c : ℤ) - 1 - ν)
    linarith
  have hGcont : ∀ ν : ℤ, Continuous (G ν) := by
    intro ν
    refine (Pc_vline_continuous n h hcpos).mul (Continuous.inv₀ (by fun_prop) fun y => ?_)
    exact pow_ne_zero _ (hne ν y)
  have hGint : ∀ ν : ℤ, Integrable (G ν) := by
    intro ν
    refine (hPint.norm.mul_const ‖((hpt ((c : ℤ) - 1 - ν)) ^ s)⁻¹‖).mono'
      (hGcont ν).aestronglyMeasurable (Eventually.of_forall fun y => ?_)
    simp only [hG]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hker ν y) (norm_nonneg _)
  have hGsum : Summable fun ν : ℤ => ∫ y : ℝ, ‖G ν y‖ := by
    refine Summable.of_nonneg_of_le (fun ν => integral_nonneg fun y => norm_nonneg _)
      (fun ν => ?_) ((summable_norm_hpt_sub (c : ℤ) hs).mul_left (∫ y : ℝ, ‖Pc n h ((c : ℝ) + y * I)‖))
    rw [← integral_mul_const]
    refine integral_mono (hGint ν).norm (hPint.norm.mul_const _) fun y => ?_
    simp only [hG]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left (hker ν y) (norm_nonneg _)
  simp_rw [hexp]
  rw [← integral_tsum_of_summable_integral_norm hGint hGsum]
  -- evaluate each term
  have hval : ∀ ν : ℤ, ∫ y : ℝ, G ν y =
      if (c : ℤ) ≤ ν then -2 * π * Dc n h (s - 1) (hpt ν) else 0 := by
    intro ν
    have hptR : hpt ν = (((ν : ℝ) + 1 / 2 : ℝ) : ℂ) := hpt_eq_ofReal ν
    split_ifs with hν
    · have hx : (c : ℝ) < (ν : ℝ) + 1 / 2 := by
        have : ((c : ℤ) : ℝ) ≤ (ν : ℝ) := by exact_mod_cast hν
        push_cast at this
        linarith
      have := vline_Pc_right hV hh hcpos (s - 1) hx
      rw [show s - 1 + 1 = s by omega] at this
      simp only [hG]
      rw [hptR, this]
    · have hx : (ν : ℝ) + 1 / 2 < (c : ℝ) := by
        have : (ν : ℝ) + 1 ≤ ((c : ℤ) : ℝ) := by
          have : ν + 1 ≤ (c : ℤ) := by omega
          exact_mod_cast this
        push_cast at this
        linarith
      simp only [hG]
      rw [hptR]
      exact vline_Pc_left hV hh hcpos hx (by omega)
  simp_rw [hval]
  have hinj : Function.Injective (fun l : ℕ => (c : ℤ) + (l : ℤ)) := by
    intro a b hab
    simp only [add_right_inj, Nat.cast_inj] at hab
    exact hab
  rw [← hinj.tsum_eq (f := fun ν : ℤ => if (c : ℤ) ≤ ν then -2 * π * Dc n h (s - 1) (hpt ν) else 0)]
  · simp only [le_add_iff_nonneg_right, Nat.cast_nonneg, ↓reduceIte]
    rw [tsum_mul_left]
  · intro ν hν
    simp only [Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hν
    obtain ⟨hcν, _⟩ := hν
    refine ⟨(ν - c).toNat, ?_⟩
    simp only
    omega


/-! ## The three kernel integrals of configuration E -/

/-- `I_s(m) = ∫ Pc(m+iy) K_s(m+iy) dy` for configuration E (`n = 40 m`). -/
def Iker (m s : ℕ) : ℂ :=
  ∫ y : ℝ, Pc (40 * m) (fun p => (m : ℤ) * hE p) ((m : ℝ) + y * I) *
    kerS s ((m : ℝ) + y * I)

/-- `c_i` of configuration E as a complex number. -/
def cc (m i : ℕ) : ℂ := (csum (40 * m) (fun p => (m : ℤ) * hE p) i : ℂ)

theorem Icc_one_six : Finset.Icc (1 : ℕ) 6 = {1, 2, 3, 4, 5, 6} := by decide

theorem sum_Icc_six (f : ℕ → ℂ) :
    ∑ i ∈ Finset.Icc 1 6, f i = f 1 + f 2 + f 3 + f 4 + f 5 + f 6 := by
  rw [Icc_one_six]
  simp [Finset.sum_insert]
  ring

theorem cc_vanish (hV : Stmt_CoeffVanish) (m : ℕ) :
    cc m 1 = 0 ∧ cc m 2 = 0 ∧ cc m 4 = 0 ∧ cc m 6 = 0 := by
  have hadm := admissible_E m
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [cc, hV.c1 _ _ hadm]
  · simp [cc, hV.ceven _ _ hadm 2 (by decide)]
  · simp [cc, hV.ceven _ _ hadm 4 (by decide)]
  · simp [cc, hV.ceven _ _ hadm 6 (by decide)]

theorem Iker_two (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (m : ℕ) (hm : 1 ≤ m) :
    Iker m 2 = π * (3 * cc m 3 * Zc 4 + 5 * cc m 5 * Zc 6) := by
  obtain ⟨h1, h2, h4, h6⟩ := cc_vanish hV m
  unfold Iker
  rw [vline_Pc_kerS hV (admissible_E m) m hm (le_refl 2)]
  have e2 := tsum_Dc_hpt_eq_two_mul hPF hV m (j := 1) (Or.inl rfl)
  have e3 := tsum_Dc_hpt (40 * m) (fun p => (m : ℤ) * hE p) (j := 1) le_rfl
  rw [e2, sum_Icc_six] at e3
  have hc : ∀ i, (csum (40 * m) (fun p => (m : ℤ) * hE p) i : ℂ) = cc m i := fun i => rfl
  simp only [hc, h1, h2, h4, h6] at e3
  have ha3 : ((acoef 3 1 : ℚ) : ℂ) = -3 := by norm_num [acoef]
  have ha5 : ((acoef 5 1 : ℚ) : ℂ) = -5 := by norm_num [acoef]
  rw [ha3, ha5] at e3
  norm_num at e3
  show -2 * (π : ℂ) * ∑' l : ℕ, Dc (40 * m) (fun p => (m : ℤ) * hE p) 1 (hpt ((m : ℤ) + l)) = _
  linear_combination (-π) * e3

theorem Iker_four (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (m : ℕ) (hm : 1 ≤ m) :
    Iker m 4 = π * (10 * cc m 3 * Zc 6 + 35 * cc m 5 * Zc 8) := by
  obtain ⟨h1, h2, h4, h6⟩ := cc_vanish hV m
  unfold Iker
  rw [vline_Pc_kerS hV (admissible_E m) m hm (by norm_num : 2 ≤ 4)]
  have e2 := tsum_Dc_hpt_eq_two_mul hPF hV m (j := 3) (Or.inr rfl)
  have e3 := tsum_Dc_hpt (40 * m) (fun p => (m : ℤ) * hE p) (j := 3) (by norm_num)
  rw [e2, sum_Icc_six] at e3
  have hc : ∀ i, (csum (40 * m) (fun p => (m : ℤ) * hE p) i : ℂ) = cc m i := fun i => rfl
  simp only [hc, h1, h2, h4, h6] at e3
  have ha3 : ((acoef 3 3 : ℚ) : ℂ) = -10 := by norm_num [acoef, Nat.choose]
  have ha5 : ((acoef 5 3 : ℚ) : ℂ) = -35 := by norm_num [acoef, Nat.choose]
  rw [ha3, ha5] at e3
  norm_num at e3
  show -2 * (π : ℂ) * ∑' l : ℕ, Dc (40 * m) (fun p => (m : ℤ) * hE p) 3 (hpt ((m : ℤ) + l)) = _
  linear_combination (-π) * e3

theorem Iker_five (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (m : ℕ) (hm : 1 ≤ m) :
    Iker m 5 = -2 * π * (15 * cc m 3 * Zp 7 + 70 * cc m 5 * Zp 9 +
      (rho0 (40 * m) (fun p => (m : ℤ) * hE p) : ℂ) / 24) := by
  obtain ⟨h1, h2, h4, h6⟩ := cc_vanish hV m
  unfold Iker
  rw [vline_Pc_kerS hV (admissible_E m) m hm (by norm_num : 2 ≤ 5)]
  have e3 := tsum_Dc4 hPF m
  rw [sum_Icc_six] at e3
  have hc : ∀ i, (csum (40 * m) (fun p => (m : ℤ) * hE p) i : ℂ) = cc m i := fun i => rfl
  simp only [hc, h1, h2, h4, h6] at e3
  have ha3 : ((acoef 3 4 : ℚ) : ℂ) = 15 := by norm_num [acoef, Nat.choose]
  have ha5 : ((acoef 5 4 : ℚ) : ℂ) = 70 := by norm_num [acoef, Nat.choose]
  rw [ha3, ha5] at e3
  norm_num at e3
  show -2 * (π : ℂ) * ∑' l : ℕ, Dc (40 * m) (fun p => (m : ℤ) * hE p) 4 (hpt ((m : ℤ) + l)) = _
  rw [e3]

/-! ## Cauchy–Schwarz for the half-integer zeta values -/

theorem norm_inv_hpt_pow_mul (k : ℕ) (ν : ℤ) :
    ‖((hpt ν) ^ (2 * k))⁻¹‖ = ‖((hpt ν) ^ 2)⁻¹‖ ^ k := by
  rw [norm_inv, norm_inv, norm_pow, norm_pow, pow_mul, inv_pow]

theorem summable_zabs_term {s : ℕ} (hs : 2 ≤ s) :
    Summable fun ν : ℤ => ‖((hpt ν) ^ s)⁻¹‖ := by
  have := summable_norm_kerS_term 0 hs
  refine this.congr fun ν => ?_
  rw [norm_inv, norm_inv, norm_pow, norm_pow, zero_sub, norm_neg]

theorem zabs_pos {s : ℕ} (hs : 2 ≤ s) : 0 < zabs s := by
  unfold zabs
  refine (summable_zabs_term hs).tsum_pos (fun ν => norm_nonneg _) 0 ?_
  rw [norm_inv, norm_pow]
  have : 0 < ‖hpt 0‖ := lt_of_lt_of_le (by norm_num) (half_le_norm_hpt 0)
  positivity

theorem Zc_even (k : ℕ) : Zc (2 * k) = ((zabs (2 * k) : ℝ) : ℂ) := by
  unfold Zc zabs
  rw [Complex.ofReal_tsum]
  congr 1
  ext ν
  rw [hpt_eq_ofReal, norm_inv, norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have e : |(ν : ℝ) + 1 / 2| ^ (2 * k) = ((ν : ℝ) + 1 / 2) ^ (2 * k) := by
    rw [pow_mul, sq_abs, ← pow_mul]
  rw [e]
  push_cast
  ring

theorem zabs_cs : zabs 6 ^ 2 ≤ zabs 4 * zabs 8 := by
  set b : ℤ → ℝ := fun ν => ‖((hpt ν) ^ 2)⁻¹‖ with hb
  have hbk : ∀ k : ℕ, (fun ν : ℤ => ‖((hpt ν) ^ (2 * k))⁻¹‖) = fun ν => b ν ^ k := by
    intro k
    ext ν
    exact norm_inv_hpt_pow_mul k ν
  have hs : ∀ k : ℕ, 1 ≤ k → Summable fun ν : ℤ => b ν ^ k := by
    intro k hk
    rw [← hbk k]
    exact summable_zabs_term (by omega)
  have z4 : zabs 4 = ∑' ν : ℤ, b ν ^ 2 := by
    unfold zabs
    rw [show (4 : ℕ) = 2 * 2 from rfl, hbk 2]
  have z6 : zabs 6 = ∑' ν : ℤ, b ν ^ 3 := by
    unfold zabs
    rw [show (6 : ℕ) = 2 * 3 from rfl, hbk 3]
  have z8 : zabs 8 = ∑' ν : ℤ, b ν ^ 4 := by
    unfold zabs
    rw [show (8 : ℕ) = 2 * 4 from rfl, hbk 4]
  have key : ∀ x y : ℝ, 0 ≤ x ^ 2 * zabs 8 - 2 * x * y * zabs 6 + y ^ 2 * zabs 4 := by
    intro x y
    have e : ∀ ν, b ν ^ 2 * (b ν * x - y) ^ 2 =
        x ^ 2 * b ν ^ 4 - 2 * x * y * b ν ^ 3 + y ^ 2 * b ν ^ 2 := by intro ν; ring
    have hsum : ∑' ν : ℤ, b ν ^ 2 * (b ν * x - y) ^ 2 =
        x ^ 2 * zabs 8 - 2 * x * y * zabs 6 + y ^ 2 * zabs 4 := by
      simp_rw [e]
      rw [Summable.tsum_add (((hs 4 (by norm_num)).mul_left _).sub ((hs 3 (by norm_num)).mul_left _))
        ((hs 2 (by norm_num)).mul_left _),
        Summable.tsum_sub ((hs 4 (by norm_num)).mul_left _) ((hs 3 (by norm_num)).mul_left _),
        tsum_mul_left, tsum_mul_left, tsum_mul_left, z4, z6, z8]
    rw [← hsum]
    exact tsum_nonneg fun ν => by positivity
  have h8 : 0 < zabs 8 := zabs_pos (by norm_num)
  have := key (zabs 6) (zabs 8)
  nlinarith

/-- The determinant `105 Z₄ Z₈ - 50 Z₆²` is positive. -/
theorem det_pos : 0 < 105 * zabs 4 * zabs 8 - 50 * zabs 6 ^ 2 := by
  have h4 := zabs_pos (s := 4) (by norm_num)
  have h8 := zabs_pos (s := 8) (by norm_num)
  have := zabs_cs
  nlinarith [mul_pos h4 h8]

/-- The determinant as a real number. -/
def detZ : ℝ := 105 * zabs 4 * zabs 8 - 50 * zabs 6 ^ 2

theorem detZ_pos : 0 < detZ := det_pos

theorem cc3_eq (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (m : ℕ) (hm : 1 ≤ m) :
    cc m 3 * ((π : ℂ) * (detZ : ℂ)) =
      35 * (zabs 8 : ℂ) * Iker m 2 - 5 * (zabs 6 : ℂ) * Iker m 4 := by
  have Z4 : Zc 4 = (zabs 4 : ℂ) := Zc_even 2
  have Z6 : Zc 6 = (zabs 6 : ℂ) := Zc_even 3
  have Z8 : Zc 8 = (zabs 8 : ℂ) := Zc_even 4
  rw [Iker_two hPF hV m hm, Iker_four hPF hV m hm, Z4, Z6, Z8, detZ]
  push_cast
  ring

theorem cc5_eq (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (m : ℕ) (hm : 1 ≤ m) :
    cc m 5 * ((π : ℂ) * (detZ : ℂ)) =
      3 * (zabs 4 : ℂ) * Iker m 4 - 10 * (zabs 6 : ℂ) * Iker m 2 := by
  have Z4 : Zc 4 = (zabs 4 : ℂ) := Zc_even 2
  have Z6 : Zc 6 = (zabs 6 : ℂ) := Zc_even 3
  have Z8 : Zc 8 = (zabs 8 : ℂ) := Zc_even 4
  rw [Iker_two hPF hV m hm, Iker_four hPF hV m hm, Z4, Z6, Z8, detZ]
  push_cast
  ring

theorem rho_eq (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (m : ℕ) (hm : 1 ≤ m) :
    (rho0 (40 * m) (fun p => (m : ℤ) * hE p) : ℂ) =
      -24 * (Iker m 5 / (2 * π) + 15 * cc m 3 * Zp 7 + 70 * cc m 5 * Zp 9) := by
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [Iker_five hPF hV m hm]
  field_simp
  ring

theorem norm_piD : ‖(π : ℂ) * (detZ : ℂ)‖ = π * detZ := by
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos Real.pi_pos, abs_of_pos detZ_pos]

theorem norm_cc3_le (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (m : ℕ) (hm : 1 ≤ m) :
    ‖cc m 3‖ ≤ (35 * zabs 8 * ‖Iker m 2‖ + 5 * zabs 6 * ‖Iker m 4‖) / (π * detZ) := by
  have hpos : 0 < π * detZ := mul_pos Real.pi_pos detZ_pos
  rw [le_div_iff₀ hpos, ← norm_piD, ← norm_mul, cc3_eq hPF hV m hm]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (zabs_pos (by norm_num)),
    abs_of_pos (zabs_pos (by norm_num))]
  have h35 : ‖(35 : ℂ)‖ = 35 := by norm_num
  have h5 : ‖(5 : ℂ)‖ = 5 := by norm_num
  rw [h35, h5]

theorem norm_cc5_le (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (m : ℕ) (hm : 1 ≤ m) :
    ‖cc m 5‖ ≤ (3 * zabs 4 * ‖Iker m 4‖ + 10 * zabs 6 * ‖Iker m 2‖) / (π * detZ) := by
  have hpos : 0 < π * detZ := mul_pos Real.pi_pos detZ_pos
  rw [le_div_iff₀ hpos, ← norm_piD, ← norm_mul, cc5_eq hPF hV m hm]
  refine le_trans (norm_sub_le _ _) ?_
  rw [norm_mul, norm_mul, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (zabs_pos (by norm_num)),
    abs_of_pos (zabs_pos (by norm_num))]
  have h3 : ‖(3 : ℂ)‖ = 3 := by norm_num
  have h10 : ‖(10 : ℂ)‖ = 10 := by norm_num
  rw [h3, h10]

theorem norm_rho_le (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (m : ℕ) (hm : 1 ≤ m) :
    ‖(rho0 (40 * m) (fun p => (m : ℤ) * hE p) : ℂ)‖ ≤
      24 * (‖Iker m 5‖ / (2 * π) + 15 * ‖cc m 3‖ * ‖Zp 7‖ + 70 * ‖cc m 5‖ * ‖Zp 9‖) := by
  rw [rho_eq hPF hV m hm, norm_mul]
  have h24 : ‖(-24 : ℂ)‖ = 24 := by norm_num
  rw [h24]
  gcongr
  refine le_trans (norm_add₃_le) ?_
  have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
  have h15 : ‖(15 : ℂ)‖ = 15 := by norm_num
  have h70 : ‖(70 : ℂ)‖ = 70 := by norm_num
  simp only [norm_div, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
    h2, h15, h70, le_refl]

theorem abs_Z7_eq (m : ℕ) :
    |(Z7 (40 * m) (fun p => (m : ℤ) * hE p) : ℝ)| = 46080 * ‖cc m 3‖ := by
  have e : (Z7 (40 * m) (fun p => (m : ℤ) * hE p) : ℝ) =
      46080 * (csum (40 * m) (fun p => (m : ℤ) * hE p) 3 : ℝ) := by
    rw [Z7]; push_cast; ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 46080), cc, Complex.norm_ratCast]

theorem abs_Z9_eq (m : ℕ) :
    |(Z9 (40 * m) (fun p => (m : ℤ) * hE p) : ℝ)| = 860160 * ‖cc m 5‖ := by
  have e : (Z9 (40 * m) (fun p => (m : ℤ) * hE p) : ℝ) =
      860160 * (csum (40 * m) (fun p => (m : ℤ) * hE p) 5 : ℝ) := by
    rw [Z9]; push_cast; ring
  rw [e, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 860160), cc, Complex.norm_ratCast]

theorem abs_rho_eq (m : ℕ) :
    |(rho0 (40 * m) (fun p => (m : ℤ) * hE p) : ℝ)| =
      ‖(rho0 (40 * m) (fun p => (m : ℤ) * hE p) : ℂ)‖ := by
  rw [Complex.norm_ratCast]

/-- **Coefficient bound**: `|ρ₀|, |Z₇|, |Z₉| ≤ K (|I₂| + |I₄| + |I₅|)`. -/
theorem coeff_le_Iker (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ, 1 ≤ m →
      |(rho0 (40 * m) (fun p => (m : ℤ) * hE p) : ℝ)| ≤
          K * (‖Iker m 2‖ + ‖Iker m 4‖ + ‖Iker m 5‖) ∧
        |(Z7 (40 * m) (fun p => (m : ℤ) * hE p) : ℝ)| ≤
          K * (‖Iker m 2‖ + ‖Iker m 4‖ + ‖Iker m 5‖) ∧
        |(Z9 (40 * m) (fun p => (m : ℤ) * hE p) : ℝ)| ≤
          K * (‖Iker m 2‖ + ‖Iker m 4‖ + ‖Iker m 5‖) := by
  have hz4 : 0 < zabs 4 := zabs_pos (by norm_num)
  have hz6 : 0 < zabs 6 := zabs_pos (by norm_num)
  have hz8 : 0 < zabs 8 := zabs_pos (by norm_num)
  have hpD : 0 < π * detZ := mul_pos Real.pi_pos detZ_pos
  -- constants
  obtain ⟨A, hA0, hA⟩ : ∃ A : ℝ, 0 ≤ A ∧ A = (35 * zabs 8 + 5 * zabs 6) / (π * detZ) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ B = (3 * zabs 4 + 10 * zabs 6) / (π * detZ) :=
    ⟨_, by positivity, rfl⟩
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 ≤ C ∧
      C = 24 * (1 / (2 * π) + 15 * A * ‖Zp 7‖ + 70 * B * ‖Zp 9‖) := ⟨_, by positivity, rfl⟩
  refine ⟨46080 * A + 860160 * B + C, by positivity, fun m hm => ?_⟩
  obtain ⟨S, hS⟩ : ∃ S : ℝ, S = ‖Iker m 2‖ + ‖Iker m 4‖ + ‖Iker m 5‖ := ⟨_, rfl⟩
  rw [← hS]
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hI2 : ‖Iker m 2‖ ≤ S := by rw [hS]; linarith [norm_nonneg (Iker m 4), norm_nonneg (Iker m 5)]
  have hI4 : ‖Iker m 4‖ ≤ S := by rw [hS]; linarith [norm_nonneg (Iker m 2), norm_nonneg (Iker m 5)]
  have hI5 : ‖Iker m 5‖ ≤ S := by rw [hS]; linarith [norm_nonneg (Iker m 2), norm_nonneg (Iker m 4)]
  have hn3 : ‖cc m 3‖ ≤ A * S := by
    refine le_trans (norm_cc3_le hPF hV m hm) ?_
    rw [hA, div_mul_eq_mul_div]
    gcongr
    nlinarith
  have hn5 : ‖cc m 5‖ ≤ B * S := by
    refine le_trans (norm_cc5_le hPF hV m hm) ?_
    rw [hB, div_mul_eq_mul_div]
    gcongr
    nlinarith
  have hnr : ‖(rho0 (40 * m) (fun p => (m : ℤ) * hE p) : ℂ)‖ ≤ C * S := by
    refine le_trans (norm_rho_le hPF hV m hm) ?_
    rw [hC]
    have t1 : ‖Iker m 5‖ / (2 * π) ≤ 1 / (2 * π) * S := by
      rw [div_eq_mul_one_div, mul_comm]
      exact mul_le_mul_of_nonneg_left hI5 (by positivity)
    have t2 : 15 * ‖cc m 3‖ * ‖Zp 7‖ ≤ 15 * A * ‖Zp 7‖ * S := by
      have := mul_le_mul_of_nonneg_left hn3 (by positivity : (0 : ℝ) ≤ 15 * ‖Zp 7‖)
      nlinarith
    have t3 : 70 * ‖cc m 5‖ * ‖Zp 9‖ ≤ 70 * B * ‖Zp 9‖ * S := by
      have := mul_le_mul_of_nonneg_left hn5 (by positivity : (0 : ℝ) ≤ 70 * ‖Zp 9‖)
      nlinarith
    nlinarith
  have hAS : 0 ≤ A * S := mul_nonneg hA0 hS0
  have hBS : 0 ≤ B * S := mul_nonneg hB0 hS0
  have hCS : 0 ≤ C * S := mul_nonneg hC0 hS0
  refine ⟨?_, ?_, ?_⟩
  · rw [abs_rho_eq]
    nlinarith
  · rw [abs_Z7_eq]
    nlinarith
  · rw [abs_Z9_eq]
    nlinarith

-- (part: growth_land)

/-! ## Derivative and continuity in `y` -/

theorem Gf_hasDerivAt_y (a : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => Gf a y) (Real.arctan (a / y)) y := by
  have hpos : 0 < a ^ 2 + y ^ 2 := by positivity
  have h1 : HasDerivAt (fun y : ℝ => a ^ 2 + y ^ 2) (2 * y) y := by
    simpa using (hasDerivAt_pow 2 y).const_add (a ^ 2)
  have h2 := (h1.log hpos.ne').const_mul (a / 2)
  have h3 : HasDerivAt (fun y : ℝ => a / y) (-a / y ^ 2) y := by
    have := (hasDerivAt_inv hy.ne').const_mul a
    convert this using 1
    · ext y'; simp [div_eq_mul_inv]
    · field_simp
  have h4 := h3.arctan
  have h5 := (hasDerivAt_id y).mul h4
  have h6 := (h2.add h5).sub_const a
  convert h6 using 1
  · ext y'; simp [Gf]
  · simp only [id]
    field_simp
    ring

theorem continuous_mul_arctan_div (a : ℝ) : Continuous fun y : ℝ => y * Real.arctan (a / y) := by
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  by_cases hy₀ : y₀ = 0
  · subst hy₀
    show Tendsto (fun y : ℝ => y * Real.arctan (a / y)) (𝓝 0) (𝓝 (0 * Real.arctan (a / 0)))
    rw [zero_mul]
    refine squeeze_zero_norm (a := fun y : ℝ => |y| * (π / 2)) (fun y => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul]
      gcongr
      exact abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
    · have : Tendsto (fun y : ℝ => |y| * (π / 2)) (𝓝 0) (𝓝 (|0| * (π / 2))) :=
        (continuous_abs.mul continuous_const).continuousAt
      simpa using this
  · exact continuousAt_id.mul (Real.continuous_arctan.continuousAt.comp
      (continuousAt_const.div continuousAt_id hy₀))

theorem continuous_Gf_y (a : ℝ) : Continuous fun y : ℝ => Gf a y := by
  unfold Gf
  have hlog : Continuous fun y : ℝ => a / 2 * Real.log (a ^ 2 + y ^ 2) := by
    by_cases ha : a = 0
    · subst ha; simp only [zero_div, zero_mul]; exact continuous_const
    · have h1 : 0 < a ^ 2 := by positivity
      have hc : Continuous fun y : ℝ => a ^ 2 + y ^ 2 := by fun_prop
      refine continuous_const.mul (hc.log fun y => ?_)
      have h2 := sq_nonneg y
      exact ne_of_gt (by linarith)
  exact (hlog.add (continuous_mul_arctan_div a)).sub continuous_const

theorem continuous_PhiE_y (ξ : ℝ) : Continuous fun y : ℝ => PhiE ξ y := by
  unfold PhiE
  refine (continuous_finsetSum _ fun p _ => ?_).sub (continuous_const.mul ?_)
  · exact (continuous_Gf_y _).sub (continuous_Gf_y _)
  · exact (continuous_Gf_y _).sub (continuous_Gf_y _)

/-- The `y`-derivative of the landscape function. -/
def dPhiE (ξ y : ℝ) : ℝ :=
  ∑ p : Fin 6, (Real.arctan ((ξ + 1 + etaE p) / y) - Real.arctan ((ξ - etaE p) / y)) -
    6 * (Real.arctan ((ξ + 1) / y) - Real.arctan (ξ / y))

theorem PhiE_hasDerivAt_y (ξ : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => PhiE ξ y) (dPhiE ξ y) y := by
  unfold PhiE dPhiE
  refine HasDerivAt.sub (HasDerivAt.fun_sum fun p _ => ?_) (HasDerivAt.const_mul 6 ?_)
  · exact (Gf_hasDerivAt_y _ hy).sub (Gf_hasDerivAt_y _ hy)
  · exact (Gf_hasDerivAt_y _ hy).sub (Gf_hasDerivAt_y _ hy)

theorem dPhiE_le (ξ : ℝ) {y : ℝ} (hy : 0 < y) : dPhiE ξ y ≤ 6 * π := by
  unfold dPhiE
  have h1 : ∀ p : Fin 6, Real.arctan ((ξ + 1 + etaE p) / y) - Real.arctan ((ξ - etaE p) / y) ≤ π := by
    intro p
    have := Real.arctan_lt_pi_div_two ((ξ + 1 + etaE p) / y)
    have := Real.neg_pi_div_two_lt_arctan ((ξ - etaE p) / y)
    linarith
  have h2 : 0 ≤ Real.arctan ((ξ + 1) / y) - Real.arctan (ξ / y) := by
    have : ξ / y ≤ (ξ + 1) / y := by gcongr; linarith
    have := Real.arctan_strictMono.monotone this
    linarith
  have h3 : ∑ p : Fin 6, (Real.arctan ((ξ + 1 + etaE p) / y) - Real.arctan ((ξ - etaE p) / y)) ≤
      ∑ _p : Fin 6, π := Finset.sum_le_sum fun p _ => h1 p
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h3
  push_cast at h3
  linarith

/-- **(L-i)** `Φ(ξ, η) ≤ Φ(ξ, 0) + 6πη` for `η ≥ 0`. -/
theorem PhiE_le_add (ξ : ℝ) {η : ℝ} (hη : 0 ≤ η) : PhiE ξ η ≤ PhiE ξ 0 + 6 * π * η := by
  rcases eq_or_lt_of_le hη with h | h
  · subst h; simp
  · obtain ⟨ζ, hζ, hζeq⟩ := exists_hasDerivAt_eq_slope (fun y => PhiE ξ y) (dPhiE ξ) h
      (continuous_PhiE_y ξ).continuousOn (fun y hy => PhiE_hasDerivAt_y ξ hy.1)
    have h1 := dPhiE_le ξ hζ.1
    rw [hζeq, sub_zero, div_le_iff₀ h] at h1
    linarith

/-! ## The bound for large `y` (second-order Taylor in the first variable) -/

theorem hasDerivAt_logsq_half (η : ℝ) (hη : 0 < η) (a : ℝ) :
    HasDerivAt (fun a : ℝ => Real.log (a ^ 2 + η ^ 2) / 2) (a / (a ^ 2 + η ^ 2)) a := by
  have hpos : 0 < a ^ 2 + η ^ 2 := by positivity
  have h1 : HasDerivAt (fun a : ℝ => a ^ 2 + η ^ 2) (2 * a) a := by
    simpa using (hasDerivAt_pow 2 a).add_const (η ^ 2)
  have h2 := (h1.log hpos.ne').div_const 2
  convert h2 using 1
  field_simp

theorem abs_div_sq_add_le (η : ℝ) (hη : 0 < η) (a : ℝ) : |a / (a ^ 2 + η ^ 2)| ≤ 1 / (2 * η) := by
  have hpos : 0 < a ^ 2 + η ^ 2 := by positivity
  rw [abs_div, abs_of_pos hpos, div_le_div_iff₀ hpos (by positivity)]
  nlinarith [sq_nonneg (|a| - η), sq_abs a, abs_nonneg a]

/-- Lipschitz bound for `a ↦ log(a² + η²)/2`. -/
theorem logsq_half_lip (η : ℝ) (hη : 0 < η) (u v : ℝ) :
    |Real.log (u ^ 2 + η ^ 2) / 2 - Real.log (v ^ 2 + η ^ 2) / 2| ≤ |u - v| / (2 * η) := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := fun a : ℝ => Real.log (a ^ 2 + η ^ 2) / 2)
    (f' := fun a => a / (a ^ 2 + η ^ 2)) (s := Set.univ) (C := 1 / (2 * η))
    (fun a _ => (hasDerivAt_logsq_half η hη a).hasDerivWithinAt)
    (fun a _ => by rw [Real.norm_eq_abs]; exact abs_div_sq_add_le η hη a) convex_univ
    (Set.mem_univ v) (Set.mem_univ u)
  simp only [Real.norm_eq_abs] at this
  calc _ ≤ 1 / (2 * η) * |u - v| := this
    _ = |u - v| / (2 * η) := by ring

/-- Second-order Taylor bound: `|G(ξ₀+d) - G(ξ₀) - d G'(ξ₀)| ≤ d²/(2η)`. -/
theorem Gf_taylor (η : ℝ) (hη : 0 < η) (ξ₀ d : ℝ) :
    |Gf (ξ₀ + d) η - Gf ξ₀ η - d * (Real.log (ξ₀ ^ 2 + η ^ 2) / 2)| ≤ d ^ 2 / (2 * η) := by
  set g' : ℝ := Real.log (ξ₀ ^ 2 + η ^ 2) / 2 with hg'
  set H : ℝ → ℝ := fun u => Gf (ξ₀ + u) η - u * g' with hH
  have hHd : ∀ u : ℝ, HasDerivAt H (Real.log ((ξ₀ + u) ^ 2 + η ^ 2) / 2 - g') u := by
    intro u
    have h1 : HasDerivAt (fun u => Gf (ξ₀ + u) η) (Real.log ((ξ₀ + u) ^ 2 + η ^ 2) / 2) u := by
      exact (Gf_hasDerivAt hη (ξ₀ + u)).comp_const_add ξ₀ u
    have h2 : HasDerivAt (fun u : ℝ => u * g') g' u := by
      simpa using (hasDerivAt_id u).mul_const g'
    exact h1.sub h2
  have hbound : ∀ u ∈ Set.uIcc 0 d, ‖Real.log ((ξ₀ + u) ^ 2 + η ^ 2) / 2 - g'‖ ≤ |d| / (2 * η) := by
    intro u hu
    rw [Real.norm_eq_abs, hg']
    refine le_trans (logsq_half_lip η hη (ξ₀ + u) ξ₀) ?_
    have : |ξ₀ + u - ξ₀| ≤ |d| := by
      rw [add_sub_cancel_left]
      rcases le_total 0 d with hd | hd
      · rw [Set.uIcc_of_le hd] at hu
        rw [abs_of_nonneg hu.1, abs_of_nonneg hd]; exact hu.2
      · rw [Set.uIcc_of_ge hd] at hu
        rw [abs_of_nonpos hu.2, abs_of_nonpos hd]; linarith [hu.1]
    gcongr
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := H) (s := Set.uIcc 0 d)
    (fun u _ => (hHd u).hasDerivWithinAt) hbound (convex_uIcc 0 d) Set.left_mem_uIcc
    Set.right_mem_uIcc
  simp only [hH, Real.norm_eq_abs, add_zero, zero_mul, sub_zero] at this
  have e : Gf (ξ₀ + d) η - d * g' - Gf ξ₀ η = Gf (ξ₀ + d) η - Gf ξ₀ η - d * g' := by ring
  rw [e] at this
  calc _ ≤ |d| / (2 * η) * |d| := this
    _ = d ^ 2 / (2 * η) := by rw [← sq_abs d]; ring

/-- **(L-iv)** For `η ≥ 1`, `Φ(ξ, η) ≤ 4`. -/
theorem PhiE_le_four (ξ : ℝ) {η : ℝ} (hη : 1 ≤ η) : PhiE ξ η ≤ 4 := by
  have hη0 : 0 < η := by linarith
  set ξ₀ := ξ + 1 / 2 with hξ₀
  set g' : ℝ := Real.log (ξ₀ ^ 2 + η ^ 2) / 2 with hg'
  set E : ℝ → ℝ := fun d => Gf (ξ₀ + d) η - Gf ξ₀ η - d * g' with hEdef
  have hEb : ∀ d, |E d| ≤ d ^ 2 / 2 := by
    intro d
    refine le_trans (Gf_taylor η hη0 ξ₀ d) ?_
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [sq_nonneg d]
  have hrepr : PhiE ξ η = ∑ p : Fin 6, (E (1 / 2 + etaE p) - E (-(1 / 2) - etaE p)) -
      6 * (E (1 / 2) - E (-(1 / 2))) := by
    have a1 : ∀ p : Fin 6, ξ₀ + (1 / 2 + etaE p) = ξ + 1 + etaE p := by intro p; rw [hξ₀]; ring
    have a2 : ∀ p : Fin 6, ξ₀ + (-(1 / 2) - etaE p) = ξ - etaE p := by intro p; rw [hξ₀]; ring
    have a3 : ξ₀ + 1 / 2 = ξ + 1 := by rw [hξ₀]; ring
    have a4 : ξ₀ + -(1 / 2) = ξ := by rw [hξ₀]; ring
    simp only [hEdef, a1, a2, a3, a4]
    unfold PhiE
    simp only [Fin.sum_univ_six]
    linear_combination (2 * g') * sum_etaE_six
  rw [hrepr]
  have hb : ∀ p : Fin 6, |E (1 / 2 + etaE p) - E (-(1 / 2) - etaE p)| ≤ (1 / 2 + etaE p) ^ 2 := by
    intro p
    refine le_trans (abs_sub _ _) ?_
    have h1 := hEb (1 / 2 + etaE p)
    have h2 := hEb (-(1 / 2) - etaE p)
    have : (-(1 / 2) - etaE p) ^ 2 = (1 / 2 + etaE p) ^ 2 := by ring
    rw [this] at h2
    linarith
  have hb2 : |E (1 / 2) - E (-(1 / 2))| ≤ 1 / 4 := by
    refine le_trans (abs_sub _ _) ?_
    have h1 := hEb (1 / 2)
    have h2 := hEb (-(1 / 2))
    norm_num at h1 h2
    linarith
  have hsum : ∑ p : Fin 6, (E (1 / 2 + etaE p) - E (-(1 / 2) - etaE p)) ≤
      ∑ p : Fin 6, (1 / 2 + etaE p) ^ 2 :=
    Finset.sum_le_sum fun p _ => le_trans (le_abs_self _) (hb p)
  have hval : ∑ p : Fin 6, (1 / 2 + etaE p) ^ 2 = 2764 / 1600 := by
    simp only [Fin.sum_univ_six, etaE, hE]
    norm_num
  have h6 : -(6 * (E (1 / 2) - E (-(1 / 2)))) ≤ 6 / 4 := by
    have := neg_abs_le (E (1 / 2) - E (-(1 / 2)))
    linarith
  linarith

/-! ## The numerical landscape inequalities (certificate) -/

/-- **(L-ii) Real profile.** `Φ(ξ, 0) ≤ -0.72` on `[1/40, 7/100]` (true maximum `≈ -0.8005`, at
`ξ ≈ 1/40`). -/
theorem landscape_real : ∀ ξ ∈ Set.Icc (1 / 40 : ℝ) (7 / 100), PhiE ξ 0 ≤ -18 / 25 := by
  sorry

/-- **(L-iii) Vertical line.** `Φ(7/100, η) - 2πη ≤ -0.72` for `0 < η ≤ 1` (true maximum
`≈ -0.7812` at `η ≈ 0.031`: the saddle point). -/
theorem landscape_vert : ∀ η ∈ Set.Ioc (0 : ℝ) 1, PhiE (7 / 100) η - 2 * π * η ≤ -18 / 25 := by
  sorry

-- (part: growth_contour)

/-! ## Elementary norm comparisons -/

theorem norm_le_of_re_eq {z w : ℂ} (hre : z.re = w.re) (him : |z.im| ≤ |w.im|) : ‖z‖ ≤ ‖w‖ := by
  rw [Complex.norm_eq_sqrt_sq_add_sq, Complex.norm_eq_sqrt_sq_add_sq]
  apply Real.sqrt_le_sqrt
  rw [hre]
  have h2 : z.im ^ 2 ≤ w.im ^ 2 := by
    rw [← sq_abs z.im, ← sq_abs w.im]
    exact pow_le_pow_left₀ (abs_nonneg _) him 2
  linarith

theorem prod_range_add_one (c : ℝ) (hc : 0 < c) (N : ℕ) :
    ∏ j ∈ range N, (c + j + 1) = (∏ j ∈ range N, (c + j)) * ((c + N) / c) := by
  induction N with
  | zero => simp [hc.ne']
  | succ N ih =>
    rw [prod_range_succ, prod_range_succ, ih]
    push_cast
    field_simp
    ring

/-- **Comparison along a short vertical segment**: `|R(c+iy)| ≤ ((c+n+1)/c)^6 |R(c+i)|` for
`0 ≤ y ≤ 1`, `c > 0`. -/
theorem norm_Rc_vert_le {n : ℕ} {h : Fin 6 → ℤ} {c : ℝ} (hc : 0 < c) {y : ℝ} (hy0 : 0 ≤ y)
    (hy1 : y ≤ 1) :
    ‖Rc n h (c + y * I)‖ ≤ ((c + n + 1) / c) ^ 6 * ‖Rc n h (c + I)‖ := by
  unfold Rc
  simp only [norm_div, norm_mul, norm_pow, norm_prod]
  have hyabs : |y| ≤ 1 := by rw [abs_of_nonneg hy0]; exact hy1
  -- numerator
  have hlin : ‖2 * ((c : ℂ) + y * I) + n‖ ≤ ‖2 * ((c : ℂ) + I) + n‖ := by
    apply norm_le_of_re_eq
    · simp
    · have e1 : (2 * ((c : ℂ) + y * I) + n).im = 2 * y := by simp
      have e2 : (2 * ((c : ℂ) + I) + n).im = 2 := by simp
      rw [e1, e2, abs_mul, abs_two]
      linarith
  have hnum : ∏ p : Fin 6, ∏ u ∈ offsets n (h p), ‖(c : ℂ) + y * I + 1 / 2 + u‖ ≤
      ∏ p : Fin 6, ∏ u ∈ offsets n (h p), ‖(c : ℂ) + I + 1 / 2 + u‖ := by
    apply Finset.prod_le_prod₀ (fun _ _ => Finset.prod_nonneg fun _ _ => norm_nonneg _)
    intro p _
    apply Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _)
    intro u _
    apply norm_le_of_re_eq
    · simp
    · have e1 : ((c : ℂ) + y * I + 1 / 2 + u).im = y := by simp
      have e2 : ((c : ℂ) + I + 1 / 2 + u).im = 1 := by simp
      rw [e1, e2, abs_one]
      exact hyabs
  -- denominator
  set P0 : ℝ := ∏ j ∈ range (n + 1), (c + j) with hP0
  have hP0pos : 0 < P0 := Finset.prod_pos fun j _ => by positivity
  have hden_y : P0 ≤ ∏ j ∈ range (n + 1), ‖(c : ℂ) + y * I + j‖ := by
    apply Finset.prod_le_prod₀ (fun j _ => by positivity)
    intro j _
    have := Complex.re_le_norm ((c : ℂ) + y * I + j)
    simpa using this
  have hden_1 : ∏ j ∈ range (n + 1), ‖(c : ℂ) + I + j‖ ≤ ∏ j ∈ range (n + 1), (c + j + 1) := by
    apply Finset.prod_le_prod₀ (fun j _ => norm_nonneg _)
    intro j _
    have e : (c : ℂ) + I + j = (((c + j : ℝ)) : ℂ) + I := by push_cast; ring
    rw [e]
    refine le_trans (norm_add_le _ _) ?_
    rw [Complex.norm_real, Complex.norm_I, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hden_1pos : 0 < ∏ j ∈ range (n + 1), ‖(c : ℂ) + I + j‖ := by
    apply Finset.prod_pos
    intro j _
    apply norm_pos_iff.mpr
    intro h0
    have := congrArg Complex.im h0
    simp at this
  have htel := prod_range_add_one c hc (n + 1)
  push_cast at htel
  rw [← hP0] at htel
  have ha1 : 0 ≤ ‖2 * ((c : ℂ) + I) + n‖ := norm_nonneg _
  have hN1 : 0 ≤ ∏ p : Fin 6, ∏ u ∈ offsets n (h p), ‖(c : ℂ) + I + 1 / 2 + u‖ :=
    Finset.prod_nonneg fun _ _ => Finset.prod_nonneg fun _ _ => norm_nonneg _
  have hQ : 0 < (c + n + 1) / c := by positivity
  have hD1le : ∏ j ∈ range (n + 1), ‖(c : ℂ) + I + j‖ ≤ P0 * ((c + n + 1) / c) := by
    refine le_trans hden_1 (le_of_eq ?_)
    rw [htel]
    ring
  calc _ ≤ ‖2 * ((c : ℂ) + I) + n‖ * (∏ p : Fin 6, ∏ u ∈ offsets n (h p),
        ‖(c : ℂ) + I + 1 / 2 + u‖) / P0 ^ 6 := by
        gcongr
    _ = ((c + n + 1) / c) ^ 6 * (‖2 * ((c : ℂ) + I) + n‖ * (∏ p : Fin 6, ∏ u ∈ offsets n (h p),
        ‖(c : ℂ) + I + 1 / 2 + u‖) / (P0 * ((c + n + 1) / c)) ^ 6) := by
        field_simp
    _ ≤ _ := by
        gcongr

/-! ## Pointwise bounds on the contour pieces -/

theorem norm_Pc_le_land (hPF : Stmt_PF) (m : ℕ) (hm : 1 ≤ m) {t : ℂ} (hre : 0 ≤ t.re)
    (him : 1 ≤ t.im) :
    ‖Pc (40 * m) (fun p => (m : ℤ) * hE p) t‖ ≤
      ‖2 * t + ((40 * m : ℕ) : ℂ)‖ * ((‖t‖ + 80 * m) ^ 6 *
        Real.exp (40 * m * PhiE (t.re / (40 * m)) (t.im / (40 * m)))) := by
  rw [Pc_eq_Rc hPF (admissible_E m) fun j _ => add_nat_ne_zero_of_im_pos (by linarith) j]
  exact norm_Rc_le m hm hre him

theorem norm_real_add_mul_I_le (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    ‖(a : ℂ) + (b : ℂ) * I‖ ≤ a + b := by
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, Complex.norm_real, Complex.norm_real, Complex.norm_I, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb, mul_one]

/-- **Piece B**: the height-one horizontal segment `x + i`, `m ≤ x ≤ 14m/5`. -/
theorem seg_B (hPF : Stmt_PF) (m : ℕ) (hm : 1 ≤ m) {x : ℝ} (hx1 : (m : ℝ) ≤ x)
    (hx2 : x ≤ 14 / 5 * m) :
    ‖Pc (40 * m) (fun p => (m : ℤ) * hE p) (x + I)‖ ≤
      48 * m * ((84 * m) ^ 6 * (Real.exp (6 * π) * Real.exp (-18 / 25 * (40 * m)))) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx0 : 0 ≤ x := by linarith
  have hre : ((x : ℂ) + I).re = x := by simp
  have him : ((x : ℂ) + I).im = 1 := by simp
  refine le_trans (norm_Pc_le_land hPF m hm (by rw [hre]; exact hx0) (by rw [him])) ?_
  rw [hre, him]
  have hN : (0 : ℝ) < 40 * m := by positivity
  have h1 : ‖2 * ((x : ℂ) + I) + ((40 * m : ℕ) : ℂ)‖ ≤ 48 * m := by
    have e : 2 * ((x : ℂ) + I) + ((40 * m : ℕ) : ℂ) =
        ((2 * x + 40 * m : ℝ) : ℂ) + ((2 : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [e]
    refine le_trans (norm_real_add_mul_I_le _ _ (by positivity) (by norm_num)) ?_
    linarith
  have h2 : ‖(x : ℂ) + I‖ + 80 * m ≤ 84 * m := by
    have : ‖(x : ℂ) + I‖ ≤ x + 1 := by
      have := norm_real_add_mul_I_le x 1 hx0 (by norm_num)
      simpa using this
    linarith
  have hξ : x / (40 * m) ∈ Set.Icc (1 / 40 : ℝ) (7 / 100) := by
    constructor
    · rw [le_div_iff₀ hN]; linarith
    · rw [div_le_iff₀ hN]; linarith
  have h3 : 40 * m * PhiE (x / (40 * m)) (1 / (40 * m)) ≤ 6 * π + -18 / 25 * (40 * m) := by
    have e1 := PhiE_le_add (x / (40 * m)) (η := 1 / (40 * m)) (by positivity)
    have e2 := landscape_real _ hξ
    have e3 : 40 * m * (6 * π * (1 / (40 * m))) = 6 * π := by field_simp
    calc 40 * m * PhiE (x / (40 * m)) (1 / (40 * m))
        ≤ 40 * m * (PhiE (x / (40 * m)) 0 + 6 * π * (1 / (40 * m))) :=
          mul_le_mul_of_nonneg_left e1 hN.le
      _ = 40 * m * PhiE (x / (40 * m)) 0 + 6 * π := by rw [mul_add, e3]
      _ ≤ 40 * m * (-18 / 25) + 6 * π := by
          linarith [mul_le_mul_of_nonneg_left e2 hN.le]
      _ = 6 * π + -18 / 25 * (40 * m) := by ring
  have h2' : 0 ≤ ‖(x : ℂ) + I‖ + 80 * m := by positivity
  calc ‖2 * ((x : ℂ) + I) + ((40 * m : ℕ) : ℂ)‖ * ((‖(x : ℂ) + I‖ + 80 * m) ^ 6 *
        Real.exp (40 * m * PhiE (x / (40 * m)) (1 / (40 * m))))
      ≤ 48 * m * ((84 * m) ^ 6 * Real.exp (6 * π + -18 / 25 * (40 * m))) := by
        gcongr
    _ = _ := by rw [Real.exp_add]

/-- **Piece A**: the short vertical segment `m + iy`, `0 ≤ y ≤ 1`. -/
theorem seg_A (hPF : Stmt_PF) (m : ℕ) (hm : 1 ≤ m) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    ‖Pc (40 * m) (fun p => (m : ℤ) * hE p) ((m : ℝ) + y * I)‖ ≤
      42 ^ 6 * (48 * m * ((84 * m) ^ 6 * (Real.exp (6 * π) * Real.exp (-18 / 25 * (40 * m))))) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  have hre : ∀ w : ℂ, w.re = m → ∀ j ≤ 40 * m, w + (j : ℂ) ≠ 0 := fun w hw j _ =>
    add_nat_ne_zero_of_re_pos (by rw [hw]; exact hm0) j
  rw [Pc_eq_Rc hPF (admissible_E m) (hre _ (by simp))]
  refine le_trans (norm_Rc_vert_le hm0 hy0 hy1) ?_
  have hPc1 := seg_B hPF m hm (x := m) le_rfl (by linarith)
  rw [Pc_eq_Rc hPF (admissible_E m) (hre _ (by simp))] at hPc1
  have hq : ((m : ℝ) + ((40 * m : ℕ) : ℝ) + 1) / m ≤ 42 := by
    rw [div_le_iff₀ hm0]; push_cast; linarith
  have hq0 : 0 ≤ ((m : ℝ) + ((40 * m : ℕ) : ℝ) + 1) / m := by positivity
  refine le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hq0 hq 6) (norm_nonneg _)) ?_
  exact mul_le_mul_of_nonneg_left hPc1 (by positivity)

/-- **Piece C₁**: the vertical line `14m/5 + iy`, `1 ≤ y ≤ 40 m`. -/
theorem seg_C1 (hPF : Stmt_PF) (m : ℕ) (hm : 1 ≤ m) {y : ℝ} (hy1 : 1 ≤ y) (hy2 : y ≤ 40 * m) :
    ‖Pc (40 * m) (fun p => (m : ℤ) * hE p) (((14 / 5 * m : ℝ) : ℂ) + y * I)‖ *
        Real.exp (-2 * π * y) ≤
      126 * m * ((123 * m) ^ 6 * Real.exp (-18 / 25 * (40 * m))) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN : (0 : ℝ) < 40 * m := by positivity
  set b : ℝ := 14 / 5 * m with hb
  have hb0 : 0 ≤ b := by positivity
  have hre : (((b : ℝ) : ℂ) + y * I).re = b := by simp
  have him : (((b : ℝ) : ℂ) + y * I).im = y := by simp
  have hP := norm_Pc_le_land hPF m hm (t := ((b : ℝ) : ℂ) + y * I) (by rw [hre]; exact hb0)
    (by rw [him]; exact hy1)
  rw [hre, him] at hP
  have h1 : ‖2 * (((b : ℝ) : ℂ) + y * I) + ((40 * m : ℕ) : ℂ)‖ ≤ 126 * m := by
    have e : 2 * (((b : ℝ) : ℂ) + y * I) + ((40 * m : ℕ) : ℂ) =
        ((2 * b + 40 * m : ℝ) : ℂ) + ((2 * y : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [e]
    refine le_trans (norm_real_add_mul_I_le _ _ (by positivity) (by linarith)) ?_
    rw [hb]; linarith
  have h2 : ‖((b : ℝ) : ℂ) + y * I‖ + 80 * m ≤ 123 * m := by
    have := norm_real_add_mul_I_le b y hb0 (by linarith)
    rw [hb] at this ⊢; linarith
  have hξ : b / (40 * m) = 7 / 100 := by rw [hb]; field_simp; ring
  rw [hξ] at hP
  have hη : y / (40 * m) ∈ Set.Ioc (0 : ℝ) 1 := by
    constructor
    · positivity
    · rw [div_le_iff₀ hN]; linarith
  have h3 : 40 * m * PhiE (7 / 100) (y / (40 * m)) + -2 * π * y ≤ -18 / 25 * (40 * m) := by
    have e2 := landscape_vert _ hη
    have e3 : 40 * m * (2 * π * (y / (40 * m))) = 2 * π * y := by field_simp
    have := mul_le_mul_of_nonneg_left e2 hN.le
    rw [mul_sub, e3] at this
    linarith
  have h2' : 0 ≤ ‖((b : ℝ) : ℂ) + y * I‖ + 80 * m := by positivity
  calc ‖Pc (40 * m) (fun p => (m : ℤ) * hE p) (((b : ℝ) : ℂ) + y * I)‖ * Real.exp (-2 * π * y)
      ≤ ‖2 * (((b : ℝ) : ℂ) + y * I) + ((40 * m : ℕ) : ℂ)‖ *
          ((‖((b : ℝ) : ℂ) + y * I‖ + 80 * m) ^ 6 *
            Real.exp (40 * m * PhiE (7 / 100) (y / (40 * m)))) * Real.exp (-2 * π * y) := by
        gcongr
    _ = ‖2 * (((b : ℝ) : ℂ) + y * I) + ((40 * m : ℕ) : ℂ)‖ *
          ((‖((b : ℝ) : ℂ) + y * I‖ + 80 * m) ^ 6 *
            Real.exp (40 * m * PhiE (7 / 100) (y / (40 * m)) + -2 * π * y)) := by
        rw [Real.exp_add]; ring
    _ ≤ 126 * m * ((123 * m) ^ 6 * Real.exp (-18 / 25 * (40 * m))) := by
        gcongr

/-- **Piece C₂**: the vertical line `14m/5 + iy`, `y ≥ 40 m`. -/
theorem seg_C2 (hPF : Stmt_PF) (m : ℕ) (hm : 1 ≤ m) {y : ℝ} (hy : 40 * m ≤ y) :
    ‖Pc (40 * m) (fun p => (m : ℤ) * hE p) (((14 / 5 * m : ℝ) : ℂ) + y * I)‖ *
        Real.exp (-2 * π * y) ≤
      4 ^ 7 * 5040 * Real.exp (160 * m - (2 * π - 1) * y) := by
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hN : (0 : ℝ) < 40 * m := by positivity
  have hy0 : 0 < y := by linarith
  set b : ℝ := 14 / 5 * m with hb
  have hb0 : 0 ≤ b := by positivity
  have hre : (((b : ℝ) : ℂ) + y * I).re = b := by simp
  have him : (((b : ℝ) : ℂ) + y * I).im = y := by simp
  have hP := norm_Pc_le_land hPF m hm (t := ((b : ℝ) : ℂ) + y * I) (by rw [hre]; exact hb0)
    (by rw [him]; linarith)
  rw [hre, him] at hP
  have h1 : ‖2 * (((b : ℝ) : ℂ) + y * I) + ((40 * m : ℕ) : ℂ)‖ ≤ 4 * y := by
    have e : 2 * (((b : ℝ) : ℂ) + y * I) + ((40 * m : ℕ) : ℂ) =
        ((2 * b + 40 * m : ℝ) : ℂ) + ((2 * y : ℝ) : ℂ) * I := by
      push_cast; ring
    rw [e]
    refine le_trans (norm_real_add_mul_I_le _ _ (by positivity) (by linarith)) ?_
    rw [hb]; linarith
  have h2 : ‖((b : ℝ) : ℂ) + y * I‖ + 80 * m ≤ 4 * y := by
    have := norm_real_add_mul_I_le b y hb0 hy0.le
    rw [hb] at this ⊢; linarith
  have hξ : b / (40 * m) = 7 / 100 := by rw [hb]; field_simp; ring
  rw [hξ] at hP
  have h3 : 40 * m * PhiE (7 / 100) (y / (40 * m)) ≤ 160 * m := by
    have hη : 1 ≤ y / (40 * m) := by rw [le_div_iff₀ hN]; linarith
    have := mul_le_mul_of_nonneg_left (PhiE_le_four (7 / 100) hη) hN.le
    linarith
  have hpow : y ^ 7 ≤ 5040 * Real.exp y := by
    have := Real.pow_div_factorial_le_exp y hy0.le 7
    rw [div_le_iff₀ (by positivity)] at this
    have h7 : ((Nat.factorial 7 : ℕ) : ℝ) = 5040 := by norm_num [Nat.factorial]
    rw [h7] at this
    linarith
  have h2' : 0 ≤ ‖((b : ℝ) : ℂ) + y * I‖ + 80 * m := by positivity
  calc ‖Pc (40 * m) (fun p => (m : ℤ) * hE p) (((b : ℝ) : ℂ) + y * I)‖ * Real.exp (-2 * π * y)
      ≤ ‖2 * (((b : ℝ) : ℂ) + y * I) + ((40 * m : ℕ) : ℂ)‖ *
          ((‖((b : ℝ) : ℂ) + y * I‖ + 80 * m) ^ 6 *
            Real.exp (40 * m * PhiE (7 / 100) (y / (40 * m)))) * Real.exp (-2 * π * y) := by
        gcongr
    _ ≤ 4 * y * ((4 * y) ^ 6 * Real.exp (160 * m)) * Real.exp (-2 * π * y) := by
        gcongr
    _ = 4 ^ 7 * y ^ 7 * (Real.exp (160 * m) * Real.exp (-2 * π * y)) := by ring
    _ ≤ 4 ^ 7 * (5040 * Real.exp y) * (Real.exp (160 * m) * Real.exp (-2 * π * y)) := by
        gcongr
    _ = 4 ^ 7 * 5040 * (Real.exp y * Real.exp (160 * m) * Real.exp (-2 * π * y)) := by ring
    _ = 4 ^ 7 * 5040 * Real.exp (160 * m - (2 * π - 1) * y) := by
        rw [← Real.exp_add, ← Real.exp_add]
        congr 2
        ring

/-! ## The contour integrand and its integrability -/

/-- The contour integrand `f_s = R_n · K_s` for configuration E. -/
def fs (m s : ℕ) (t : ℂ) : ℂ := Pc (40 * m) (fun p => (m : ℤ) * hE p) t * kerS s t

theorem fs_conj (m s : ℕ) (t : ℂ) : fs m s ((starRingEnd ℂ) t) = (starRingEnd ℂ) (fs m s t) := by
  unfold fs; rw [Pc_conj, kerS_conj, map_mul]

theorem fs_differentiableOn (m : ℕ) {s : ℕ} (hs : 2 ≤ s) :
    DifferentiableOn ℂ (fs m s) {t | 0 < t.im} :=
  (Pc_differentiableOn_im _ _).mul (kerS_differentiableOn_upper hs)

theorem fs_continuousOn_vline (m : ℕ) {s : ℕ} (hs : 2 ≤ s) (x : ℝ) :
    ContinuousOn (fun y : ℝ => fs m s (x + y * I)) (Ioi 0) := by
  refine (fs_differentiableOn m hs).continuousOn.comp (continuous_vline x).continuousOn
    fun y hy => ?_
  change 0 < ((x : ℂ) + (y : ℂ) * I).im
  rw [vline_im]; exact hy

/-- Decay of the integrand in the upper right quadrant. -/
theorem norm_fs_le_decay (hV : Stmt_CoeffVanish) (m : ℕ) {s : ℕ} {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ t : ℂ, 1 ≤ t.im → ‖kerS s t‖ ≤ κ * Real.exp (-2 * π * t.im))
    {t : ℂ} (hre : 0 ≤ t.re) (him : 1 ≤ t.im) :
    ‖fs m s t‖ ≤ κ * M2 (40 * m) (fun p => (m : ℤ) * hE p) / t.im ^ 2 := by
  have hti : t.im ≤ ‖t‖ := le_trans (le_abs_self _) (Complex.abs_im_le_norm t)
  have ht1 : 1 ≤ ‖t‖ := le_trans him hti
  have hP := norm_Pc_le_sq hV (admissible_E m) hre ht1
  have hK := hκ t him
  have hexp : Real.exp (-2 * π * t.im) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith [Real.pi_pos])
  have hM := M2_nonneg (40 * m) (fun p => (m : ℤ) * hE p)
  unfold fs
  rw [norm_mul]
  have hP' : ‖Pc (40 * m) (fun p => (m : ℤ) * hE p) t‖ ≤
      M2 (40 * m) (fun p => (m : ℤ) * hE p) / t.im ^ 2 := by
    refine le_trans hP ?_
    apply div_le_div_of_nonneg_left hM (by positivity)
    exact pow_le_pow_left₀ (by linarith) hti 2
  calc ‖Pc (40 * m) (fun p => (m : ℤ) * hE p) t‖ * ‖kerS s t‖
      ≤ M2 (40 * m) (fun p => (m : ℤ) * hE p) / t.im ^ 2 * κ := by
        gcongr
        exact le_trans hK (by nlinarith)
    _ = κ * M2 (40 * m) (fun p => (m : ℤ) * hE p) / t.im ^ 2 := by ring

theorem integrableOn_fs_vline (hV : Stmt_CoeffVanish) (m : ℕ) {s : ℕ} (hs : 2 ≤ s) {κ : ℝ}
    (hκ0 : 0 ≤ κ) (hκ : ∀ t : ℂ, 1 ≤ t.im → ‖kerS s t‖ ≤ κ * Real.exp (-2 * π * t.im))
    {x : ℝ} (hx : 0 ≤ x) :
    IntegrableOn (fun y : ℝ => fs m s (x + y * I)) (Ioi 1) := by
  set M := M2 (40 * m) (fun p => (m : ℤ) * hE p)
  have hM : 0 ≤ M := M2_nonneg _ _
  refine ((integrable_inv_one_add_sq.const_mul (2 * κ * M)).integrableOn).mono'
    (((fs_continuousOn_vline m hs x).mono (Ioi_subset_Ioi zero_le_one)).aestronglyMeasurable
      measurableSet_Ioi) ?_
  refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
  have hy1 : 1 ≤ y := le_of_lt hy
  have h := norm_fs_le_decay hV m hκ0 hκ (t := (x : ℂ) + y * I) (by simp; exact hx)
    (by simp; exact hy1)
  simp only [vline_im] at h
  refine le_trans h ?_
  have hy2 : 0 < y ^ 2 := by positivity
  rw [div_le_iff₀ hy2]
  have : (1 + y ^ 2)⁻¹ * y ^ 2 ≥ 1 / 2 := by
    rw [ge_iff_le, inv_mul_eq_div, le_div_iff₀ (by positivity)]
    nlinarith
  have hκM : 0 ≤ κ * M := mul_nonneg hκ0 hM
  nlinarith

theorem fs_top_tendsto (hV : Stmt_CoeffVanish) (m : ℕ) {s : ℕ} {κ : ℝ} (hκ0 : 0 ≤ κ)
    (hκ : ∀ t : ℂ, 1 ≤ t.im → ‖kerS s t‖ ≤ κ * Real.exp (-2 * π * t.im)) {a b : ℝ}
    (ha : 0 ≤ a) (hab : a ≤ b) :
    Tendsto (fun Y : ℝ => ∫ x in a..b, fs m s (x + Y * I)) atTop (𝓝 0) := by
  set M := M2 (40 * m) (fun p => (m : ℤ) * hE p)
  have hM : 0 ≤ M := M2_nonneg _ _
  have hlim : Tendsto (fun Y : ℝ => κ * M * |b - a| / Y ^ 2) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_pow_atTop two_ne_zero)
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with Y hY
  have hbound : ∀ x ∈ Set.uIoc a b, ‖fs m s (x + Y * I)‖ ≤ κ * M / Y ^ 2 := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have h := norm_fs_le_decay hV m hκ0 hκ (t := (x : ℂ) + Y * I) (by simp; linarith [hx.1])
      (by simp; exact hY)
    simpa using h
  refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbound) (le_of_eq ?_)
  ring

theorem fs_line_integrable (hV : Stmt_CoeffVanish) (m : ℕ) (hm : 1 ≤ m) {s : ℕ} (hs : 2 ≤ s) :
    Integrable (fun y : ℝ => fs m s ((m : ℝ) + y * I)) := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have hcont : Continuous (fun y : ℝ => fs m s ((m : ℝ) + y * I)) := by
    unfold fs
    refine (Pc_vline_continuous _ _ hm0).mul ?_
    refine continuous_iff_continuousAt.2 fun y => ?_
    have hd := kerS_differentiableAt_vline hs (m : ℤ) y
    rw [← natCast_vline] at hd
    exact ContinuousAt.comp (f := fun y : ℝ => ((m : ℝ) : ℂ) + (y : ℂ) * I) (x := y)
      hd.continuousAt (continuous_vline (m : ℝ)).continuousAt
  refine ((Pc_vline_integrable hV (admissible_E m) hm0).norm.mul_const (zabs s)).mono'
    hcont.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  unfold fs
  rw [norm_mul]
  gcongr
  have hk := norm_kerS_vline_le hs (m : ℤ) y
  rwa [← natCast_vline] at hk

/-! ## The bound on `I_s` -/

theorem integral_exp_affine_Ioi (A β c : ℝ) (hβ : 0 < β) :
    ∫ y in Ioi c, Real.exp (A - β * y) = Real.exp (A - β * c) / β := by
  have e : ∀ y : ℝ, Real.exp (A - β * y) = Real.exp A * Real.exp (-β * y) := by
    intro y; rw [← Real.exp_add]; ring_nf
  simp_rw [e]
  rw [integral_const_mul, integral_exp_mul_Ioi (by linarith) c, neg_div_neg_eq]
  ring

theorem integrableOn_exp_affine_Ioi (A β c : ℝ) (hβ : 0 < β) :
    IntegrableOn (fun y : ℝ => Real.exp (A - β * y)) (Ioi c) := by
  have e : ∀ y : ℝ, Real.exp (A - β * y) = Real.exp A * Real.exp (-β * y) := by
    intro y; rw [← Real.exp_add]; ring_nf
  simp_rw [e]
  exact (exp_neg_integrableOn_Ioi c hβ).const_mul _

/-- **Main contour bound**: `|I_s(m)| ≤ C m^8 e^{-0.72 · 40 m}`. -/
theorem Iker_le (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) {s : ℕ} (hs : 2 ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ m : ℕ, 1 ≤ m →
      ‖Iker m s‖ ≤ C * (m : ℝ) ^ 8 * Real.exp (-18 / 25 * (40 * m)) := by
  obtain ⟨κ, hκ0, hκ⟩ := kerS_decay hs
  have hz : 0 ≤ zabs s := tsum_nonneg fun _ => norm_nonneg _
  set E6 := Real.exp (6 * π) with hE6
  have hE60 : 0 ≤ E6 := (Real.exp_pos _).le
  have h2pi : 0 < 2 * π - 1 := by linarith [Real.pi_gt_three]
  set CA : ℝ := 42 ^ 6 * 48 * 84 ^ 6 * E6 * zabs s with hCA
  set CB : ℝ := 2 * κ * 48 * 84 ^ 6 * E6 with hCB
  set CC1 : ℝ := 40 * κ * 126 * 123 ^ 6 with hCC1
  set CC2 : ℝ := κ * 4 ^ 7 * 5040 / (2 * π - 1) with hCC2
  have hCA0 : 0 ≤ CA := by positivity
  have hCB0 : 0 ≤ CB := by positivity
  have hCC10 : 0 ≤ CC1 := by positivity
  have hCC20 : 0 ≤ CC2 := by positivity
  refine ⟨2 * (CA + CB + CC1 + CC2), by positivity, fun m hm => ?_⟩
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hm0 : (0 : ℝ) < m := by linarith
  set g := Real.exp (-18 / 25 * (40 * m)) with hg
  have hg0 : 0 ≤ g := (Real.exp_pos _).le
  have hm7 : (m : ℝ) ^ 7 ≤ (m : ℝ) ^ 8 := pow_le_pow_right₀ hm1 (by norm_num)
  have hm8 : (1 : ℝ) ≤ (m : ℝ) ^ 8 := one_le_pow₀ hm1
  have hmm8 : (m : ℝ) ^ 2 * (m : ℝ) ^ 6 = (m : ℝ) ^ 8 := by ring
  set c : ℝ := (m : ℝ) with hc
  set b : ℝ := 14 / 5 * m with hb
  have hcb : c ≤ b := by rw [hc, hb]; linarith
  have hint := fs_line_integrable hV m hm hs
  -- Step 1: conjugation symmetry
  have h1 : ‖Iker m s‖ ≤ 2 * ‖∫ y in Ioi (0 : ℝ), fs m s (c + y * I)‖ :=
    norm_integral_line_conj_le (fs_conj m s) hint
  -- Step 2: split at height 1
  have hsplit : ∫ y in Ioi (0 : ℝ), fs m s (c + y * I) =
      (∫ y in Ioc (0 : ℝ) 1, fs m s (c + y * I)) + ∫ y in Ioi (1 : ℝ), fs m s (c + y * I) := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi hint.integrableOn
      hint.integrableOn, Ioc_union_Ioi_eq_Ioi zero_le_one]
  -- Step 3: shift the upper half-line to `Re t = b`
  have hia := integrableOn_fs_vline hV m hs hκ0 hκ (x := c) hm0.le
  have hib := integrableOn_fs_vline hV m hs hκ0 hκ (x := b) (by positivity)
  have hshift := halfstrip_shift hcb (fs_differentiableOn m hs) hia hib
    (fs_top_tendsto hV m hκ0 hκ hm0.le hcb)
  have h3 : ‖∫ y in Ioi (1 : ℝ), fs m s (c + y * I)‖ ≤
      ‖∫ x in c..b, fs m s (x + (1 : ℝ) * I)‖ + ‖∫ y in Ioi (1 : ℝ), fs m s (b + y * I)‖ := by
    have := congrArg norm hshift
    rw [norm_mul, Complex.norm_I, one_mul] at this
    rw [this]
    refine le_trans (norm_add_le _ _) ?_
    rw [norm_mul, Complex.norm_I, one_mul]
  -- Step 4: split the far line at height `40 m`
  have hN1 : (1 : ℝ) ≤ 40 * m := by linarith
  have hsplit2 : ∫ y in Ioi (1 : ℝ), fs m s (b + y * I) =
      (∫ y in Ioc (1 : ℝ) (40 * m), fs m s (b + y * I)) +
        ∫ y in Ioi (40 * (m : ℝ)), fs m s (b + y * I) := by
    rw [← setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi
      (hib.mono_set Ioc_subset_Ioi_self) (hib.mono_set (Ioi_subset_Ioi hN1)),
      Ioc_union_Ioi_eq_Ioi hN1]
  -- Step 5: the four bounds
  have hA : ‖∫ y in Ioc (0 : ℝ) 1, fs m s (c + y * I)‖ ≤ CA * (m : ℝ) ^ 8 * g := by
    have hbd : ∀ y ∈ Ioc (0 : ℝ) 1, ‖fs m s (c + y * I)‖ ≤
        42 ^ 6 * (48 * m * ((84 * m) ^ 6 * (E6 * g))) * zabs s := by
      intro y hy
      unfold fs
      rw [norm_mul]
      have hk := norm_kerS_vline_le hs (m : ℤ) y
      rw [← natCast_vline] at hk
      exact mul_le_mul (seg_A hPF m hm hy.1.le hy.2) hk (norm_nonneg _) (by positivity)
    refine le_trans (norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top hbd) ?_
    rw [Real.volume_real_Ioc_of_le zero_le_one, sub_zero, mul_one, hCA]
    have : 42 ^ 6 * (48 * m * ((84 * m) ^ 6 * (E6 * g))) * zabs s =
        42 ^ 6 * 48 * 84 ^ 6 * E6 * zabs s * (m : ℝ) ^ 7 * g := by ring
    rw [this]
    gcongr
  have hB : ‖∫ x in c..b, fs m s (x + (1 : ℝ) * I)‖ ≤ CB * (m : ℝ) ^ 8 * g := by
    have hbd : ∀ x ∈ Set.uIoc c b, ‖fs m s (x + (1 : ℝ) * I)‖ ≤
        48 * m * ((84 * m) ^ 6 * (E6 * g)) * κ := by
      intro x hx
      rw [Set.uIoc_of_le hcb] at hx
      have e : (x : ℂ) + ((1 : ℝ) : ℂ) * I = (x : ℂ) + I := by simp
      rw [e]
      unfold fs
      rw [norm_mul]
      have hk := hκ ((x : ℂ) + I) (by simp)
      have hk' : ‖kerS s ((x : ℂ) + I)‖ ≤ κ := by
        refine le_trans hk ?_
        have : Real.exp (-2 * π * ((x : ℂ) + I).im) ≤ 1 :=
          Real.exp_le_one_iff.mpr (by simp; linarith [Real.pi_pos])
        nlinarith
      exact mul_le_mul (seg_B hPF m hm hx.1.le (by rw [hb] at hx; exact hx.2)) hk' (norm_nonneg _)
        (by positivity)
    refine le_trans (intervalIntegral.norm_integral_le_of_norm_le_const hbd) ?_
    have hlen : |b - c| ≤ 2 * m := by
      rw [abs_of_nonneg (by linarith)]; rw [hb, hc]; linarith
    calc 48 * m * ((84 * m) ^ 6 * (E6 * g)) * κ * |b - c|
        ≤ 48 * m * ((84 * m) ^ 6 * (E6 * g)) * κ * (2 * m) := by gcongr
      _ = CB * ((m : ℝ) ^ 2 * (m : ℝ) ^ 6) * g := by rw [hCB]; ring
      _ = CB * (m : ℝ) ^ 8 * g := by rw [hmm8]
  have hC1 : ‖∫ y in Ioc (1 : ℝ) (40 * m), fs m s (b + y * I)‖ ≤ CC1 * (m : ℝ) ^ 8 * g := by
    have hbd : ∀ y ∈ Ioc (1 : ℝ) (40 * m), ‖fs m s (b + y * I)‖ ≤
        κ * (126 * m * ((123 * m) ^ 6 * g)) := by
      intro y hy
      unfold fs
      rw [norm_mul]
      have hk := hκ ((b : ℂ) + y * I) (by simp; exact hy.1.le)
      simp only [vline_im] at hk
      have hC := seg_C1 hPF m hm hy.1.le hy.2
      rw [← hb] at hC
      calc ‖Pc (40 * m) (fun p => (m : ℤ) * hE p) ((b : ℂ) + y * I)‖ * ‖kerS s ((b : ℂ) + y * I)‖
          ≤ ‖Pc (40 * m) (fun p => (m : ℤ) * hE p) ((b : ℂ) + y * I)‖ *
              (κ * Real.exp (-2 * π * y)) := by gcongr
        _ = κ * (‖Pc (40 * m) (fun p => (m : ℤ) * hE p) ((b : ℂ) + y * I)‖ *
              Real.exp (-2 * π * y)) := by ring
        _ ≤ κ * (126 * m * ((123 * m) ^ 6 * g)) := by gcongr
    refine le_trans (norm_setIntegral_le_of_norm_le_const measure_Ioc_lt_top hbd) ?_
    rw [Real.volume_real_Ioc_of_le hN1]
    calc κ * (126 * m * ((123 * m) ^ 6 * g)) * (40 * m - 1)
        ≤ κ * (126 * m * ((123 * m) ^ 6 * g)) * (40 * m) := by
          gcongr; linarith
      _ = CC1 * ((m : ℝ) ^ 2 * (m : ℝ) ^ 6) * g := by rw [hCC1]; ring
      _ = CC1 * (m : ℝ) ^ 8 * g := by rw [hmm8]
  have hC2 : ‖∫ y in Ioi (40 * (m : ℝ)), fs m s (b + y * I)‖ ≤ CC2 * (m : ℝ) ^ 8 * g := by
    have hbd : ∀ᵐ (y : ℝ) ∂(volume.restrict (Ioi (40 * (m : ℝ)))), ‖fs m s (b + y * I)‖ ≤
        κ * (4 ^ 7 * 5040) * Real.exp (160 * m - (2 * π - 1) * y) := by
      refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun y hy => ?_)
      have hy' : 40 * (m : ℝ) ≤ y := le_of_lt hy
      unfold fs
      rw [norm_mul]
      have hk := hκ ((b : ℂ) + y * I) (by simp; linarith)
      simp only [vline_im] at hk
      have hC := seg_C2 hPF m hm hy'
      rw [← hb] at hC
      calc ‖Pc (40 * m) (fun p => (m : ℤ) * hE p) ((b : ℂ) + y * I)‖ * ‖kerS s ((b : ℂ) + y * I)‖
          ≤ ‖Pc (40 * m) (fun p => (m : ℤ) * hE p) ((b : ℂ) + y * I)‖ *
              (κ * Real.exp (-2 * π * y)) := by gcongr
        _ = κ * (‖Pc (40 * m) (fun p => (m : ℤ) * hE p) ((b : ℂ) + y * I)‖ *
              Real.exp (-2 * π * y)) := by ring
        _ ≤ κ * (4 ^ 7 * 5040 * Real.exp (160 * m - (2 * π - 1) * y)) := by gcongr
        _ = κ * (4 ^ 7 * 5040) * Real.exp (160 * m - (2 * π - 1) * y) := by ring
    have hgint : Integrable (fun y : ℝ => κ * (4 ^ 7 * 5040) * Real.exp (160 * m - (2 * π - 1) * y))
        (volume.restrict (Ioi (40 * (m : ℝ)))) :=
      (integrableOn_exp_affine_Ioi (160 * m) (2 * π - 1) (40 * m) h2pi).const_mul _
    refine le_trans (norm_integral_le_of_norm_le hgint hbd) ?_
    rw [integral_const_mul, integral_exp_affine_Ioi _ _ _ h2pi]
    have hexp : Real.exp (160 * m - (2 * π - 1) * (40 * m)) ≤ g := by
      rw [hg]
      apply Real.exp_le_exp.mpr
      nlinarith [Real.pi_gt_three]
    calc κ * (4 ^ 7 * 5040) * (Real.exp (160 * m - (2 * π - 1) * (40 * m)) / (2 * π - 1))
        ≤ κ * (4 ^ 7 * 5040) * (g / (2 * π - 1)) := by gcongr
      _ = CC2 * 1 * g := by rw [hCC2]; ring
      _ ≤ CC2 * (m : ℝ) ^ 8 * g := by gcongr
  -- combine
  rw [hsplit] at h1
  rw [hsplit2] at h3
  have hsum : ‖Iker m s‖ ≤ 2 * (CA * (m : ℝ) ^ 8 * g + CB * (m : ℝ) ^ 8 * g +
      CC1 * (m : ℝ) ^ 8 * g + CC2 * (m : ℝ) ^ 8 * g) := by
    refine le_trans h1 ?_
    gcongr
    refine le_trans (norm_add_le _ _) ?_
    have h3' := le_trans h3 (add_le_add le_rfl (norm_add_le _ _))
    linarith
  refine le_trans hsum (le_of_eq ?_)
  ring

-- (part: growth_final)

/-! ## Assembly: `Stmt_Growth configE gE` -/

/-- Polynomials are eventually dominated by `exp(δ m)`. -/
theorem eventually_poly_le_exp (A : ℝ) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ m : ℕ in atTop, A * (m : ℝ) ^ 8 ≤ Real.exp (δ * m) := by
  have hA1 : 0 < |A| + 1 := by positivity
  have h1 := (isLittleO_pow_exp_pos_mul_atTop 8 hδ).def (c := 1 / (|A| + 1)) (by positivity)
  have h2 := tendsto_natCast_atTop_atTop.eventually h1
  filter_upwards [h2] with m hm
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity),
    abs_of_pos (Real.exp_pos _)] at hm
  have hm8 : 0 ≤ (m : ℝ) ^ 8 := by positivity
  calc A * (m : ℝ) ^ 8 ≤ (|A| + 1) * (m : ℝ) ^ 8 := by
        gcongr; linarith [le_abs_self A]
    _ ≤ (|A| + 1) * (1 / (|A| + 1) * Real.exp (δ * m)) := by gcongr
    _ = Real.exp (δ * m) := by field_simp

/-- **GAP 1 for configuration E** (modulo the two numerical landscape inequalities). -/
theorem growth_main (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) : Stmt_Growth configE gE := by
  obtain ⟨K, hK0, hK⟩ := coeff_le_Iker hPF hV
  obtain ⟨C2, hC20, hC2⟩ := Iker_le hPF hV (s := 2) le_rfl
  obtain ⟨C4, hC40, hC4⟩ := Iker_le hPF hV (s := 4) (by norm_num)
  obtain ⟨C5, hC50, hC5⟩ := Iker_le hPF hV (s := 5) (by norm_num)
  intro ε hε
  have hδ : 0 < 40 * ε := by positivity
  filter_upwards [eventually_poly_le_exp (K * (C2 + C4 + C5)) hδ, eventually_ge_atTop 1]
    with m hpoly hm
  have hn : ((configE.n m : ℕ) : ℝ) = 40 * m := by rw [configE_n]; push_cast; ring
  have hh : configE.h m = fun p => (m : ℤ) * hE p := rfl
  rw [hn, hh, configE_n]
  set g := Real.exp (-18 / 25 * (40 * m)) with hg
  have hI : ‖Iker m 2‖ + ‖Iker m 4‖ + ‖Iker m 5‖ ≤ (C2 + C4 + C5) * (m : ℝ) ^ 8 * g := by
    have e2 := hC2 m hm
    have e4 := hC4 m hm
    have e5 := hC5 m hm
    rw [← hg] at e2 e4 e5
    linarith
  have hkey : K * (‖Iker m 2‖ + ‖Iker m 4‖ + ‖Iker m 5‖) ≤ Real.exp ((gE + ε) * (40 * m)) := by
    calc K * (‖Iker m 2‖ + ‖Iker m 4‖ + ‖Iker m 5‖)
        ≤ K * ((C2 + C4 + C5) * (m : ℝ) ^ 8 * g) := by gcongr
      _ = (K * (C2 + C4 + C5) * (m : ℝ) ^ 8) * g := by ring
      _ ≤ Real.exp (40 * ε * m) * g := by gcongr
      _ = Real.exp ((gE + ε) * (40 * m)) := by
          rw [hg, ← Real.exp_add, gE]
          congr 1
          ring
  obtain ⟨h1, h2, h3⟩ := hK m hm
  exact ⟨le_trans h1 hkey, le_trans h2 hkey, le_trans h3 hkey⟩

end GrowthAux

/-- **GAP 1 (growth) for configuration E.**  For every `ε > 0`, eventually
`|ρ₀|, |Z₇|, |Z₉| ≤ exp((-0.72 + ε) n)`.  The proof (`GrowthAux.growth_main`) is complete except
for the two explicit numerical landscape inequalities `GrowthAux.landscape_real` and
`GrowthAux.landscape_vert`. -/
theorem Growth_proof (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) : Stmt_Growth configE gE :=
  GrowthAux.growth_main hPF hV

end Zeta2.Pair

end
