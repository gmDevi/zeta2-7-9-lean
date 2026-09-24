import Zeta2Lean.Pair.Statements

/-!
# L1 for the pair: only `ζ₂(7)` and `ζ₂(9)` survive

gap: '' (routine).

**Task.** Prove `Stmt_L1` from `Stmt_GenLinearForm` and `Stmt_CoeffVanish`: for admissible `(n, h)`
the Riemann sums of `integrand n h` converge to `ρ₀ + 60 c₃ J₆ + 210 c₅ J₈`.

**Informal proof.** By definition `integrand n h = genIntegrand 6 n (rcoef n h)`,
`rho0 n h = genRho0 6 n (rcoef n h)` and `csum n h i = genCsum n (rcoef n h) i` (all `rfl`).
`Stmt_GenLinearForm 6 n (rcoef n h)` gives the limit
  `ρ₀ + ∑_{i=1}^{6} (i)(i+1)(i+2) c_i J_{i+3}`.
By `Stmt_CoeffVanish` (`c1` and `ceven` with `i = 2, 4, 6`) the terms `i = 1, 2, 4, 6` vanish,
leaving `(3·4·5) c₃ J₆ + (5·6·7) c₅ J₈ = 60 c₃ J₆ + 210 c₅ J₈`.  (No `J_odd = 0` is needed: the
coefficients of `J₄, J₅, J₇, J₉` are zero.)  Rewrite the limit value (`HasVolkenborn` is `Tendsto`;
prove equality of the values and use `▸` / `convert`).

**Lean hints.** Expand `∑ i ∈ Icc 1 6` with `Finset.sum_Icc_succ_top` (six times) or
`decide`-rewriting `Icc 1 6 = {1,2,3,4,5,6}` and `Finset.sum_insert`; `Even` witnesses via
`⟨1, rfl⟩`, `⟨2, rfl⟩`, `⟨3, rfl⟩`; then `simp`, `push_cast`, `ring`.

**Numerical check.** `python/pair_mirror.py`, section "Stmt_GenLinearForm / Stmt_L1".
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Pair

theorem L1_proof (hG : Stmt_GenLinearForm) (hV : Stmt_CoeffVanish) : Stmt_L1 := by
  sorry

end Zeta2.Pair

end
