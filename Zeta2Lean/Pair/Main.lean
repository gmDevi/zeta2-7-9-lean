import Zeta2Lean.Pair.Assembly
import Zeta2Lean.Proofs.JConvergence
import Zeta2Lean.Proofs.Translation
import Zeta2Lean.Proofs.Criterion
import Zeta2Lean.Proofs.DeltaCalculus
import Zeta2Lean.Proofs.DeltaFunctions
import Zeta2Lean.Pair.Proofs.GenLinearForm
import Zeta2Lean.Pair.Proofs.PartialFractions
import Zeta2Lean.Pair.Proofs.CoeffVanish
import Zeta2Lean.Pair.Proofs.LinearForm
import Zeta2Lean.Pair.Proofs.IntegrandTaylor
import Zeta2Lean.Pair.Proofs.CrudeIntegrality
import Zeta2Lean.Pair.Proofs.Valuation
import Zeta2Lean.Pair.Proofs.NonvanishingLS
import Zeta2Lean.Pair.Proofs.Growth
import Zeta2Lean.Pair.Proofs.Denominators
import Zeta2Lean.Pair.Proofs.Nonvanishing

set_option linter.style.header false

/-!
# Zeta2Lean.Pair.Main — at least one of `ζ₂(7)`, `ζ₂(9)` is irrational, assuming PNT

Wires the proofs of the routine statements and of the three gap statements into
`main_of_stmts` (`Pair/Assembly.lean`).  The prime number theorem remains a hypothesis here; it is
discharged in `Pair/Unconditional.lean`.

* `zeta2_7_9_not_both_rational_of_gaps` — any configuration, any rates `g + δ < 12 log 2`;
  hypotheses: PNT and the three gap statements `Stmt_Growth cfg g`, `Stmt_Denominators cfg δ`,
  `Stmt_Nonvanishing cfg`.
* `zeta2_7_9_not_both_rational` — configuration E with the rates `gE = -0.72`, `deltaE = 9`
  (`marginE`), with the three gap statements as hypotheses.
* `zeta2_7_9_not_both_rational_LS` — the same with GAP 3 replaced by the purely arithmetic
  Lai–Sprang condition `Stmt_LaiSprangCond configE`.
* `zeta2_7_9_not_both_rational_uncond` — the gap proofs (`Pair/Proofs/Growth.lean`,
  `Denominators.lean`, `Nonvanishing.lean`) plugged in as well: only PNT remains as a hypothesis.

Reused from the `{7,9,11}` repository: `JConv_proof`, `Translation_proof`, `Criterion_proof`,
`Delta_proof`, `DeltaFun_proof` (files `Zeta2Lean/Proofs/*.lean`, identical to that repository's;
see `BLUEPRINT_PAIR.md`).

Dependency graph (see `BLUEPRINT_PAIR.md`):
* `L1 ← GenLinearForm (← JConv, Translation), CoeffVanish (← PF)`
* `Valuation ← IntegrandTaylor (← PF), Delta, DeltaFun`
* gaps: `Growth`, `Denominators`, `Nonvanishing` (or `LaiSprangCond` + `NonvanishingLS ← L1`)
-/

namespace Zeta2.Pair

/-- The routine part, proved: `Stmt_L1`. -/
theorem L1_full : Stmt_L1 :=
  L1_proof (GenLinearForm_proof JConv_proof Translation_proof) (CoeffVanish_proof PF_proof)

/-- The routine part, proved: `Stmt_Valuation` (GAP 4). -/
theorem Valuation_full : Stmt_Valuation :=
  Valuation_proof (IntegrandTaylor_proof PF_proof) Delta_proof (DeltaFun_proof Delta_proof)

/-- **Main theorem, general form.**  For any configuration and any rates with
`g + δ < 12 log 2`: assuming PNT and the three gap statements, the Riemann sums defining every
`J s` converge and `ζ₂(7)`, `ζ₂(9)` are not both rational. -/
theorem zeta2_7_9_not_both_rational_of_gaps (hPNT : PNT_Stmt) (cfg : Config) (g δ : ℝ)
    (hmargin : g + δ < 12 * Real.log 2) (hGrowth : Stmt_Growth cfg g)
    (hDen : Stmt_Denominators cfg δ) (hNV : Stmt_Nonvanishing cfg) : PairStatement :=
  main_of_stmts cfg g δ hmargin JConv_proof L1_full Valuation_full Criterion_proof hGrowth hDen hNV
    hPNT

/-- **Main theorem, conditional form** (configuration E, rates `gE = -0.72`, `deltaE = 9`).
Assuming the prime number theorem and the three gap statements, `ζ₂(7)` and `ζ₂(9)` are not both
rational.  (`zeta2_7_9_not_both_rational_uncond` below discharges the gap statements.) -/
theorem zeta2_7_9_not_both_rational (hPNT : PNT_Stmt) (hGrowth : Stmt_Growth configE gE)
    (hDen : Stmt_Denominators configE deltaE) (hNV : Stmt_Nonvanishing configE) :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧
      ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q)) :=
  zeta2_7_9_not_both_rational_of_gaps hPNT configE gE deltaE marginE hGrowth hDen hNV

/-- Variant: GAP 3 replaced by the arithmetic Lai–Sprang condition. -/
theorem zeta2_7_9_not_both_rational_LS (hPNT : PNT_Stmt) (hGrowth : Stmt_Growth configE gE)
    (hDen : Stmt_Denominators configE deltaE) (hLS : Stmt_LaiSprangCond configE) :
    PairStatement :=
  zeta2_7_9_not_both_rational hPNT hGrowth hDen (Nonvanishing_of_LaiSprang configE L1_full hLS)

/-- Everything plugged in: only the prime number theorem remains as a hypothesis (it is discharged
in `Pair/Unconditional.lean`). -/
theorem zeta2_7_9_not_both_rational_uncond (hPNT : PNT_Stmt) : PairStatement :=
  zeta2_7_9_not_both_rational hPNT
    (Growth_proof PF_proof (CoeffVanish_proof PF_proof))
    (Denominators_proof PF_proof (CoeffVanish_proof PF_proof) CrudeInt_proof)
    (Nonvanishing_proof L1_full (IntegrandTaylor_proof PF_proof) Delta_proof
      (DeltaFun_proof Delta_proof) PF_proof (CoeffVanish_proof PF_proof) CrudeInt_proof)

end Zeta2.Pair

#print axioms Zeta2.Pair.zeta2_7_9_not_both_rational
#print axioms Zeta2.Pair.zeta2_7_9_not_both_rational_uncond
