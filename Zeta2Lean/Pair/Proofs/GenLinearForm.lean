import Zeta2Lean.Pair.Statements

/-!
# Generic linear form (pair blueprint; LSZ Lemma 3.3, proof.md Lemma 1 before any vanishing)

gap: '' (routine).

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
(`(i)₃ (i+3) = (i)₄`), which is the claimed value after `push_cast`, `Finset.sum_sub_distrib`,
`Finset.mul_sum`, `Finset.sum_mul`, `ring`.  Finish with `HasVolkenborn` being a `Tendsto`: prove
the two limit values equal, then `convert`/`▸`, and the two integrands equal by `funext` +
`push_cast`.

**Lean hints.** `HasVolkenborn.sum`, `HasVolkenborn.const_mul`, `HasVolkenborn.add`,
`halfPow_eq_cast`, `volkenbornSum_sum` (all in `Zeta2Lean/Defs.lean`, namespace `Zeta2`);
`Rat.cast_sum`, `Rat.cast_mul`, `Rat.cast_pow`, `Rat.cast_inv`, `Rat.cast_natCast`,
`Finset.sum_congr`, `Finset.mul_sum`, `Finset.sum_sub_distrib`.  Work with `a` general: do **not**
expand `Icc 1 a`.  The sibling project's `Zeta2Lean/Proofs/LinearForm.lean` (once proved) does the
same computation for `a = 8` and can be adapted.

**Numerical check.** `python/pair_mirror.py`, section "Stmt_GenLinearForm / Stmt_L1" (random `r`,
`a = 3`: `v₂(R_N - value)` grows with `N`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Pair

theorem GenLinearForm_proof (hJ : Stmt_JConv) (hT : Stmt_Translation) : Stmt_GenLinearForm := by
  sorry

end Zeta2.Pair

end
