import Zeta2Lean.Pair.Unconditional

/-!
# Proof of the statement in `Challenge.lean`

`Zeta2.Pair.zeta2_7_9_not_both_rational_unconditional` (`Zeta2Lean/Pair/Unconditional.lean`) is
the main theorem of this repository, and its type is the statement of `Challenge.lean`. That
statement uses the definitions of `Zeta2Lean/Defs.lean`, of which `Challenge.lean` contains
verbatim copies, so this module does not restate them. Comparator checks that the two statements,
and every definition they use, are identical, and that the proof uses only the axioms `propext`,
`Classical.choice` and `Quot.sound`.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Pair

/-- **At least one of ζ₂(7), ζ₂(9) is irrational** (the statement of `Challenge.lean`). -/
theorem zeta2_7_9_not_both_rational_palomar :
    (∀ s : ℕ, HasVolkenborn (halfPow s) (J s)) ∧
      ¬ ((∃ q : ℚ, zeta2 7 = q) ∧ (∃ q : ℚ, zeta2 9 = q)) :=
  zeta2_7_9_not_both_rational_unconditional

end Zeta2.Pair

end
