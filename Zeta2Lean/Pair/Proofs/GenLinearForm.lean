import Zeta2Lean.Pair.Statements

/-!
# Generic linear form (pair blueprint; LSZ Lemma 3.3, proof.md Lemma 1 before any vanishing)

gap: '' (routine).  **Proved** (complete, kernel-checked; axioms: `propext`, `Classical.choice`,
`Quot.sound`).

**Task.** Prove `Stmt_GenLinearForm` from `Stmt_JConv` and `Stmt_Translation` (both reused from the
`{7,9,11}` project): for every pole order `a`, degree `n` and coefficient array `r : ℕ → ℕ → ℚ`,
the Riemann sums of
  `genIntegrand a n r x = ∑_{i=1}^{a} ∑_{k=0}^{n} (i)₃ r_{i,k} (x + k + 1/2)^{-(i+3)}`
converge 2-adically to
  `genRho0 a n r + ∑_{i=1}^{a} (i)₃ c_i J_{i+3}`,  `c_i = genCsum n r i = ∑_k r_{i,k}`,
  `genRho0 a n r = -∑_{i,k} (i)₄ r_{i,k} A_k^{(i+4)}`.
Nothing about the family is used; this is pure linearity.

**Informal proof.** In `ℚ_[2]`, by `halfPow_eq_cast` (in `Zeta2Lean/Defs.lean`),
  `(genIntegrand a n r x : ℚ_[2])
     = ∑_{i ∈ Icc 1 a} ∑_{k<n+1} ((i)(i+1)(i+2) r_{i,k}) · halfPow (i+3) (x + k)`
(the summand's `(((x + k : ℕ) : ℚ) + 1/2)⁻¹ ^ (i+3)` is literally `halfPow (i+3) (x+k)` after the
cast).
For each `(i, k)`: `Stmt_JConv (i+3)` gives `HasVolkenborn (halfPow (i+3)) (J (i+3))`, and
`Stmt_Translation (i+3) k` turns it into
  `HasVolkenborn (fun x => halfPow (i+3) (x + k)) (J (i+3) - (i+3) ∑_{ℓ<k} halfPow (i+4) ℓ)`.
Here `∑_{ℓ<k} halfPow (i+4) ℓ = (Ahalf k (i+4) : ℚ_[2])` (`halfPow_eq_cast`, `Rat.cast_sum`).
Linearity (`HasVolkenborn.const_mul`, `HasVolkenborn.sum` twice, in `Defs.lean`) gives the limit
  `∑_{i,k} (i)₃ r_{i,k} (J_{i+3} - (i+3) A_k^{(i+4)})
     = ∑_i (i)₃ (∑_k r_{i,k}) J_{i+3} - ∑_{i,k} (i)₄ r_{i,k} A_k^{(i+4)}`
(`(i)₃ (i+3) = (i)₄`), which is the claimed value.

**Formal proof (below).**
* `genLF_integrand_cast_halfPow`: the cast of `genIntegrand a n r x` is
  `∑_{i ∈ Icc 1 a} ∑_{k<n+1} w_{i,k} · halfPow (i+3) (x+k)` with `w_{i,k} = ((i)₃ r_{i,k} : ℚ_[2])`.
* `genLF_sum_halfPow_eq_Ahalf`: `∑_{ℓ<k} halfPow s ℓ = (Ahalf k s : ℚ_[2])`.
* `GenLinearForm_proof`: `HasVolkenborn.sum` twice + `HasVolkenborn.const_mul` of the translated
  `JConv` gives the limit `∑_{i,k} w_{i,k} (J_{i+3} - (i+3) ∑_{ℓ<k} halfPow (i+4) ℓ)`; the
  translation terms assemble to `genRho0` (`hrho`, termwise `ring`), the `J`-terms to
  `(i)₃ c_i J_{i+3}` (`hcs`, `Finset.mul_sum`), and `ring` closes (sums as atoms).  `Icc 1 a` is
  never expanded, so `a` stays general.

**Numerical check.** `python/pair_mirror.py`, section "Stmt_GenLinearForm / Stmt_L1" (random `r`,
`a = 3`: `v₂(R_N - value)` grows with `N`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Pair

/-- The generic integrand, cast to `ℚ_[2]`, in `halfPow` form:
`genIntegrand a n r x = ∑_{i=1}^{a} ∑_{k=0}^{n} (i)₃ r_{i,k} (x + k + 1/2)^{-(i+3)}`. -/
private theorem genLF_integrand_cast_halfPow (a n : ℕ) (r : ℕ → ℕ → ℚ) (x : ℕ) :
    ((genIntegrand a n r x : ℚ) : ℚ_[2]) =
      ∑ i ∈ Icc 1 a, ∑ k ∈ range (n + 1),
        ((((i : ℚ) * (i + 1) * (i + 2)) * r i k : ℚ) : ℚ_[2]) * halfPow (i + 3) (x + k) := by
  simp only [genIntegrand, halfPow_eq_cast, Rat.cast_sum, Rat.cast_mul]

/-- `∑_{ℓ<k} halfPow s ℓ = A_k^{(s)}` in `ℚ_[2]`. -/
private theorem genLF_sum_halfPow_eq_Ahalf (k s : ℕ) :
    ∑ l ∈ range k, halfPow s l = ((Ahalf k s : ℚ) : ℚ_[2]) := by
  simp only [Ahalf, halfPow_eq_cast, Rat.cast_sum]

theorem GenLinearForm_proof (hJ : Stmt_JConv) (hT : Stmt_Translation) : Stmt_GenLinearForm := by
  intro a n r
  -- `w i k = (i)₃ r_{i,k}` in `ℚ_[2]`
  set w : ℕ → ℕ → ℚ_[2] := fun i k =>
    ((((i : ℚ) * (i + 1) * (i + 2)) * r i k : ℚ) : ℚ_[2]) with hw
  -- linearity + translation: the Riemann sums converge termwise
  have key : HasVolkenborn
      (fun x => ∑ i ∈ Icc 1 a, ∑ k ∈ range (n + 1), w i k * halfPow (i + 3) (x + k))
      (∑ i ∈ Icc 1 a, ∑ k ∈ range (n + 1),
        w i k * (J (i + 3) - ((i + 3 : ℕ) : ℚ_[2]) * ∑ l ∈ range k, halfPow (i + 4) l)) := by
    refine HasVolkenborn.sum _ (fun i _ => ?_)
    refine HasVolkenborn.sum _ (fun k _ => ?_)
    exact (hT (i + 3) k (J (i + 3)) (hJ (i + 3))).const_mul (w i k)
  have e1 : (fun x => ((genIntegrand a n r x : ℚ) : ℚ_[2])) =
      fun x => ∑ i ∈ Icc 1 a, ∑ k ∈ range (n + 1), w i k * halfPow (i + 3) (x + k) := by
    funext x
    exact genLF_integrand_cast_halfPow a n r x
  -- the translation terms assemble to `ρ₀` (`(i)₃ (i+3) = (i)₄`)
  have hrho : (genRho0 a n r : ℚ_[2]) = -∑ i ∈ Icc 1 a, ∑ k ∈ range (n + 1),
      w i k * (((i + 3 : ℕ) : ℚ_[2]) * ∑ l ∈ range k, halfPow (i + 4) l) := by
    simp only [genRho0, hw, genLF_sum_halfPow_eq_Ahalf]
    push_cast
    congr 1
    refine sum_congr rfl (fun i _ => sum_congr rfl (fun k _ => ?_))
    ring
  -- the `J`-terms assemble to `(i)₃ c_i J_{i+3}`
  have hcs : ∀ i, ∑ k ∈ range (n + 1), w i k =
      ((i : ℚ_[2]) * (i + 1) * (i + 2)) * (genCsum n r i : ℚ_[2]) := by
    intro i
    simp only [hw, genCsum]
    push_cast
    rw [Finset.mul_sum]
  have e2 : ∑ i ∈ Icc 1 a, ∑ k ∈ range (n + 1),
        w i k * (J (i + 3) - ((i + 3 : ℕ) : ℚ_[2]) * ∑ l ∈ range k, halfPow (i + 4) l) =
      (genRho0 a n r : ℚ_[2]) +
        ∑ i ∈ Icc 1 a, ((i : ℚ_[2]) * (i + 1) * (i + 2)) * (genCsum n r i : ℚ_[2]) * J (i + 3) := by
    rw [hrho]
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hcs]
    ring
  rw [e1]
  rwa [e2] at key

end Zeta2.Pair

end
