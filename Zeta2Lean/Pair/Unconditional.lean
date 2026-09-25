import Zeta2Lean.Pair.Main
import Zeta2Lean.Cited.PNT

set_option linter.style.header false

/-!
# Zeta2Lean.Pair.Unconditional — `ζ₂(7)` and `ζ₂(9)` are not both rational, with no hypotheses

`Pair/Main.lean` proves `zeta2_7_9_not_both_rational_uncond : PNT_Stmt → PairStatement`, with all
three gap statements (Growth, Denominators, Nonvanishing) and every routine lemma plugged in
(configuration E: `h = (n/40)(-17, 1, 2, 3, 5, 6)`, rates `gE = -0.72`, `deltaE = 9`).  The prime
number theorem is `Zeta2.PNT_proof` (`Cited/PNT.lean`: Wiener–Ikehara, vendored from open
mathlib4 PRs, as in the sibling `{7,9,11}` project).  Composing the two gives the theorem below;
its `#print axioms` lists only `propext`, `Classical.choice`, `Quot.sound`.
-/

namespace Zeta2.Pair

/-- **Main theorem, unconditional.**  The Riemann sums defining every `J s` converge (the
Volkenborn integrals exist), and the 2-adic zeta values `ζ₂(7)`, `ζ₂(9)` are not both
rational. -/
theorem zeta2_7_9_not_both_rational_unconditional :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧
      ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q)) :=
  zeta2_7_9_not_both_rational_uncond PNT_proof

/-- The same, stated with the frozen `PairStatement`. -/
theorem pairStatement_unconditional : PairStatement :=
  zeta2_7_9_not_both_rational_unconditional

end Zeta2.Pair

#print axioms Zeta2.PNT_proof
#print axioms Zeta2.Pair.zeta2_7_9_not_both_rational_unconditional
#print axioms Zeta2.Pair.pairStatement_unconditional
