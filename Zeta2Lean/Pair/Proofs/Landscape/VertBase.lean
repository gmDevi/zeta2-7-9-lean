import Zeta2Lean.Pair.Proofs.Landscape.Numerics

/-!
# The vertical-line landscape function `Ψ(η) = Φ(7/100, η) - 2πη`: calculus

`Lf` is a verbatim copy of `GrowthAux.Gf` (`Growth.lean` identifies the two by `rfl`), and `Psi`
is `PhiE (7/100) η - 2πη` with the fourteen arguments `7/100 + 1 + η_p`, `7/100 - η_p`,
`7/100 + 1`, `7/100` evaluated to rationals.

Main tool (`Psi_le_of_deriv`): on a cell `[l, r] ⊆ [0, ∞)`, if `dPsi ≤ M` on `(l, r)` with
`M ≥ 0`, then `Ψ ≤ Ψ(l) + (r - l) M` (mean value theorem; `Ψ` is continuous on `[0, ∞)` and
differentiable on `(0, ∞)` with derivative `dPsi`).  Each summand `s_j arctan(a_j/ζ)` of `dPsi`
is monotone in `ζ` (`arctan_div_le_of_nonneg`, `arctan_div_le_of_nonpos`).
-/

open Real

noncomputable section

namespace Zeta2.Pair.Landscape

/-- Verbatim copy of `GrowthAux.Gf`. -/
def Lf (a y : ℝ) : ℝ := a / 2 * Real.log (a ^ 2 + y ^ 2) + y * Real.arctan (a / y) - a

/-- `Ψ(y) = Φ(7/100, y) - 2πy` (configuration E: `η = (-17, 1, 2, 3, 5, 6)/40`). -/
def Psi (y : ℝ) : ℝ :=
  (Lf (129 / 200) y - Lf (99 / 200) y) + (Lf (219 / 200) y - Lf (9 / 200) y) +
    (Lf (28 / 25) y - Lf (1 / 50) y) + (Lf (229 / 200) y - Lf (-(1 / 200)) y) +
    (Lf (239 / 200) y - Lf (-(11 / 200)) y) + (Lf (61 / 50) y - Lf (-(2 / 25)) y) -
    6 * (Lf (107 / 100) y - Lf (7 / 100) y) - 2 * π * y

/-- `Ψ'(y)` for `y > 0`. -/
def dPsi (y : ℝ) : ℝ :=
  (Real.arctan (129 / 200 / y) - Real.arctan (99 / 200 / y)) +
    (Real.arctan (219 / 200 / y) - Real.arctan (9 / 200 / y)) +
    (Real.arctan (28 / 25 / y) - Real.arctan (1 / 50 / y)) +
    (Real.arctan (229 / 200 / y) - Real.arctan (-(1 / 200) / y)) +
    (Real.arctan (239 / 200 / y) - Real.arctan (-(11 / 200) / y)) +
    (Real.arctan (61 / 50 / y) - Real.arctan (-(2 / 25) / y)) -
    6 * (Real.arctan (107 / 100 / y) - Real.arctan (7 / 100 / y)) - 2 * π

theorem Lf_hasDerivAt_y (a : ℝ) {y : ℝ} (hy : 0 < y) :
    HasDerivAt (fun y => Lf a y) (Real.arctan (a / y)) y := by
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
  · ext y'; simp [Lf]
  · simp only [id]
    field_simp
    ring

theorem continuous_mul_arctan_div' (a : ℝ) : Continuous fun y : ℝ => y * Real.arctan (a / y) := by
  refine continuous_iff_continuousAt.2 fun y₀ => ?_
  by_cases hy₀ : y₀ = 0
  · subst hy₀
    change Filter.Tendsto (fun y : ℝ => y * Real.arctan (a / y)) (nhds 0)
      (nhds (0 * Real.arctan (a / 0)))
    rw [zero_mul]
    refine squeeze_zero_norm (a := fun y : ℝ => |y| * (π / 2)) (fun y => ?_) ?_
    · rw [Real.norm_eq_abs, abs_mul]
      gcongr
      exact abs_le.mpr ⟨(Real.neg_pi_div_two_lt_arctan _).le, (Real.arctan_lt_pi_div_two _).le⟩
    · have : Filter.Tendsto (fun y : ℝ => |y| * (π / 2)) (nhds 0) (nhds (|0| * (π / 2))) :=
        (continuous_abs.mul continuous_const).continuousAt
      simpa using this
  · exact continuousAt_id.mul (Real.continuous_arctan.continuousAt.comp
      (continuousAt_const.div continuousAt_id hy₀))

theorem continuous_Lf_y (a : ℝ) : Continuous fun y : ℝ => Lf a y := by
  unfold Lf
  have hlog : Continuous fun y : ℝ => a / 2 * Real.log (a ^ 2 + y ^ 2) := by
    by_cases ha : a = 0
    · subst ha; simp only [zero_div, zero_mul]; exact continuous_const
    · have h1 : 0 < a ^ 2 := by positivity
      have hc : Continuous fun y : ℝ => a ^ 2 + y ^ 2 := by fun_prop
      refine continuous_const.mul (hc.log fun y => ?_)
      have h2 := sq_nonneg y
      exact ne_of_gt (by linarith)
  exact (hlog.add (continuous_mul_arctan_div' a)).sub continuous_const

theorem continuous_Psi : Continuous Psi := by
  unfold Psi
  have c := continuous_Lf_y
  refine (((((((((c _).sub (c _)).add ((c _).sub (c _))).add ((c _).sub (c _))).add
    ((c _).sub (c _))).add ((c _).sub (c _))).add ((c _).sub (c _))).sub
    (continuous_const.mul ((c _).sub (c _)))).sub (continuous_const.mul continuous_id))

theorem Psi_hasDerivAt {y : ℝ} (hy : 0 < y) : HasDerivAt Psi (dPsi y) y := by
  have d := fun a => Lf_hasDerivAt_y a hy
  have h := ((((((((d (129 / 200)).sub (d (99 / 200))).add ((d (219 / 200)).sub (d (9 / 200)))).add
    ((d (28 / 25)).sub (d (1 / 50)))).add ((d (229 / 200)).sub (d (-(1 / 200))))).add
    ((d (239 / 200)).sub (d (-(11 / 200))))).add ((d (61 / 50)).sub (d (-(2 / 25))))).sub
    (((d (107 / 100)).sub (d (7 / 100))).const_mul 6)).sub ((hasDerivAt_id y).const_mul (2 * π))
  convert h using 1
  · funext y'; simp only [Psi, Pi.add_apply, Pi.sub_apply, id]
  · simp only [dPsi, mul_one]

/-- **Mean value bound on a cell.** -/
theorem Psi_le_of_deriv {l r M : ℝ} (hl : 0 ≤ l) (hM : ∀ ζ, l < ζ → ζ < r → dPsi ζ ≤ M)
    (hM0 : 0 ≤ M) : ∀ η, l ≤ η → η ≤ r → Psi η ≤ Psi l + (r - l) * M := by
  intro η h1 h2
  rcases eq_or_lt_of_le h1 with h | h
  · subst h; nlinarith
  · obtain ⟨ζ, hζ, hζeq⟩ := exists_hasDerivAt_eq_slope Psi dPsi h continuous_Psi.continuousOn
      (fun x hx => Psi_hasDerivAt (by linarith [hx.1]))
    have h3 := hM ζ hζ.1 (by linarith [hζ.2])
    rw [hζeq, div_le_iff₀ (by linarith)] at h3
    nlinarith

/-! ## Monotonicity of `arctan (a / ζ)` in `ζ` -/

theorem arctan_div_le_of_nonneg {a y₁ y₂ V : ℝ} (ha : 0 ≤ a) (h1 : 0 < y₁) (h12 : y₁ ≤ y₂)
    (hV : a / y₁ = V) : Real.arctan (a / y₂) ≤ Real.arctan V := by
  rw [← hV]
  exact Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left ha h1 h12)

theorem arctan_div_ge_of_nonneg {a y₁ y₂ V : ℝ} (ha : 0 ≤ a) (h1 : 0 < y₁) (h12 : y₁ ≤ y₂)
    (hV : a / y₂ = V) : Real.arctan V ≤ Real.arctan (a / y₁) := by
  rw [← hV]
  exact Real.arctan_strictMono.monotone (div_le_div_of_nonneg_left ha h1 h12)

theorem arctan_div_le_of_nonpos {a y₁ y₂ V : ℝ} (ha : a ≤ 0) (h1 : 0 < y₁) (h12 : y₁ ≤ y₂)
    (hV : a / y₂ = V) : Real.arctan (a / y₁) ≤ Real.arctan V := by
  rw [← hV]
  apply Real.arctan_strictMono.monotone
  have h2 : 0 < y₂ := lt_of_lt_of_le h1 h12
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

theorem arctan_div_ge_of_nonpos {a y₁ y₂ V : ℝ} (ha : a ≤ 0) (h1 : 0 < y₁) (h12 : y₁ ≤ y₂)
    (hV : a / y₁ = V) : Real.arctan V ≤ Real.arctan (a / y₂) := by
  rw [← hV]
  apply Real.arctan_strictMono.monotone
  have h2 : 0 < y₂ := lt_of_lt_of_le h1 h12
  rw [div_le_div_iff₀ h1 h2]
  nlinarith

theorem arctan_div_ge_of_nonpos' {a y₁ y₂ V : ℝ} (ha : a ≤ 0) (h1 : 0 < y₁) (h12 : y₁ ≤ y₂)
    (hV : a / y₁ = -V) : -Real.arctan V ≤ Real.arctan (a / y₂) := by
  rw [← Real.arctan_neg]; exact arctan_div_ge_of_nonpos ha h1 h12 hV

/-! ## Evaluation of `Lf` at rational points -/

theorem Lf_eq_pos {a y Q V : ℝ} (hQ : a ^ 2 + y ^ 2 = Q) (hV : a / y = V) :
    Lf a y = a / 2 * Real.log Q + y * Real.arctan V - a := by
  unfold Lf; rw [hQ, hV]

theorem Lf_eq_neg {a y Q V : ℝ} (hQ : a ^ 2 + y ^ 2 = Q) (hV : a / y = -V) :
    Lf a y = a / 2 * Real.log Q - y * Real.arctan V - a := by
  unfold Lf; rw [hQ, hV, Real.arctan_neg]; ring

theorem Lf_eq_zero {a Q : ℝ} (hQ : a ^ 2 = Q) : Lf a 0 = a / 2 * Real.log Q - a := by
  unfold Lf; simp [hQ]

end Zeta2.Pair.Landscape
