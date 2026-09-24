import Zeta2Lean.Pair.Statements

/-!
# L1 for the pair: only `ζ₂(7)` and `ζ₂(9)` survive

gap: '' (routine).  **Proved** (2026-09-24).

**Task.** Prove `Stmt_L1` from `Stmt_GenLinearForm` and `Stmt_CoeffVanish`: for admissible `(n, h)`
the Riemann sums of `integrand n h` converge to `ρ₀ + 60 c₃ J₆ + 210 c₅ J₈`.

**Informal proof.** By definition `integrand n h = genIntegrand 6 n (rcoef n h)`,
`rho0 n h = genRho0 6 n (rcoef n h)` and `csum n h i = genCsum n (rcoef n h) i` (all `rfl`).
`Stmt_GenLinearForm 6 n (rcoef n h)` gives the limit
  `ρ₀ + ∑_{i=1}^{6} (i)(i+1)(i+2) c_i J_{i+3}`.
By `Stmt_CoeffVanish` (`c1` and `ceven` with `i = 2, 4, 6`) the terms `i = 1, 2, 4, 6` vanish,
leaving `(3·4·5) c₃ J₆ + (5·6·7) c₅ J₈ = 60 c₃ J₆ + 210 c₅ J₈`.  (No `J_odd = 0` is needed: the
coefficients of `J₄, J₅, J₇, J₉` are zero.)

**Formal proof (below).**
* `L1_limit_eq`: the limit value of `Stmt_GenLinearForm` at `a = 6`, `r = rcoef n h` equals
  `ρ₀ + 60 c₃ J₆ + 210 c₅ J₈`.  `Icc 1 6 = {1, …, 6}` by `decide`, the sum is expanded with
  `Finset.sum_insert`, `c₁ = c₂ = c₄ = c₆ = 0` are substituted, and `push_cast; ring` finishes.
* `L1_proof`: rewrite the limit of `hG 6 n (rcoef n h)` with `L1_limit_eq`; the integrand agrees
  definitionally (`integrand n h = genIntegrand 6 n (rcoef n h)`).

**Numerical check.** `python/pair_mirror.py`, section "Stmt_GenLinearForm / Stmt_L1".
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Pair

/-- The limit value of `Stmt_GenLinearForm` at `a = 6`, `r = rcoef n h` is
`ρ₀ + 60 c₃ J₆ + 210 c₅ J₈`, since `c₁ = c₂ = c₄ = c₆ = 0`. -/
private theorem L1_limit_eq (hV : Stmt_CoeffVanish) (n : ℕ) (h : Fin 6 → ℤ)
    (hh : Admissible n h) :
    (genRho0 6 n (rcoef n h) : ℚ_[2]) +
        ∑ i ∈ Icc (1 : ℕ) 6, ((i : ℚ_[2]) * (i + 1) * (i + 2)) *
          (genCsum n (rcoef n h) i : ℚ_[2]) * J (i + 3) =
      (rho0 n h : ℚ_[2]) + 60 * (csum n h 3 : ℚ_[2]) * J 6 + 210 * (csum n h 5 : ℚ_[2]) * J 8 := by
  have hIcc : (Icc (1 : ℕ) 6) = {1, 2, 3, 4, 5, 6} := by decide
  rw [hIcc, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  have h1 : genCsum n (rcoef n h) 1 = 0 := hV.c1 n h hh
  have h2 : genCsum n (rcoef n h) 2 = 0 := hV.ceven n h hh 2 ⟨1, rfl⟩
  have h4 : genCsum n (rcoef n h) 4 = 0 := hV.ceven n h hh 4 ⟨2, rfl⟩
  have h6 : genCsum n (rcoef n h) 6 = 0 := hV.ceven n h hh 6 ⟨3, rfl⟩
  simp only [h1, h2, h4, h6, rho0, csum]
  push_cast
  ring

theorem L1_proof (hG : Stmt_GenLinearForm) (hV : Stmt_CoeffVanish) : Stmt_L1 := by
  intro n h hh
  have key := hG 6 n (rcoef n h)
  rw [L1_limit_eq hV n h hh] at key
  exact key

end Zeta2.Pair

end
