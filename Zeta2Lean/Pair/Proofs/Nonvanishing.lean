import Zeta2Lean.Pair.Statements
import Zeta2Lean.Pair.Proofs.NonvanishingLS

/-!
# GAP 3 (nonvanishing): `S_n ≠ 0` infinitely often along configuration E

gap: 'nonvanishing' (open; hypothesis of the main theorem).

**Task.** Prove `Stmt_Nonvanishing configE`: if `ζ₂(7)` and `ζ₂(9)` are both rational, then for
infinitely many `m` every limit `I` of the Riemann sums of `integrand (40m) (m · hE)` is non-zero.
(The rationality hypotheses may be used; an unconditional proof simply ignores them.)
Available hypotheses: all routine statements (`Stmt_L1`, `Stmt_IntegrandTaylor`, `Stmt_Delta`,
`Stmt_DeltaFun`, `Stmt_PF`, `Stmt_CoeffVanish`, `Stmt_CrudeInt`); `Pair/Main.lean` supplies their
proofs.  (`Stmt_PF`, `Stmt_CoeffVanish`, `Stmt_CrudeInt` were added by the audit of 2026-09-24:
the root trick at the central critical zeros needs the partial-fraction identity.)

**Numerical status.** `S_n ≠ 0` at every tested `n` (`n ≤ 640`; `v₂(S_n) - 12n = -23 … -39`).

**Recommended route: the Lai–Sprang `ℓ(n)`-adic condition at `q = n - 1`** (Lai–Sprang
arXiv:2306.10393, Lemma 2.2), packaged as `Stmt_LaiSprangCond configE` (`Pair/Statements.lean`),
which implies this statement by the proved lemma `Nonvanishing_of_LaiSprang`
(`Pair/Proofs/NonvanishingLS.lean`, imported here):
```
exact Nonvanishing_of_LaiSprang configE hL1 (h : Stmt_LaiSprangCond configE)
```
It suffices to find, for every bound `B` and infinitely many `m`, a prime `q > B` with `ρ₀ ≠ 0`,
`v_q(ρ₀) < v_q(Z₇)` and `v_q(ρ₀) < v_q(Z₉)`.
* *The subsequence.* Take the `m` with `q := 40m - 1` prime: infinitely many by Dirichlet's theorem
  (in Mathlib: `Nat.frequently_atTop_prime_and_modEq`, primes `≡ 39 (mod 40)`), packaged in
  `NonvanishingLS.lean` as the proved lemmas `frequently_prime_forty_mul_sub_one` and
  `frequently_prime_forty_mul_sub_one_gt B : ∃ᶠ m in atTop, (40 m - 1).Prime ∧ B < 40 m - 1`.
* *The valuations* (track `scratchpad/pair79/nonvanishing/proof.md`, Theorem A): for `40 ∣ n`,
  `ℓ = n - 1` prime, `ℓ ≠ 91079`: `v_ℓ(ρ₀) = -9`, `v_ℓ(Z₇) ≥ -3`, `v_ℓ(Z₉) ≥ -1`; proof via
  `v_ℓ(r_{i,k}) ≥ i - 1` for `2 ≤ k ≤ n - 2` and `≥ i - 6` for `k ∈ {0, 1, n-1, n}`, and the root
  trick at the two central critical zeros (`R_n^{(4)}(t₀) = ∑_k (principal part at -k)^{(4)}(t₀)
  = 0`, from `Stmt_PF.series` at the half-integer `t₀`).  Independently confirmed by the audit
  (`python/pair_audit_independent.py` engine) at `n = 80, 240, 360`:
  `(v_ℓ ρ₀, v_ℓ Z₇, v_ℓ Z₉) = (-9, -2, 0)`.
Other primes also work numerically: at `n = 40, 80, 120, 160, 200, 400` **every** prime
`q ∈ (√n, n]` satisfies the condition, with `v_q(Z₇) - v_q(ρ₀) ≥ 6` and `v_q(Z₉) - v_q(ρ₀) ≥ 7`
(typically `7` and `9`) and `v_q(ρ₀) ∈ [-11, -4]` (`scratchpad/pair79/architect/
laisprang_check.out`; audit engine).  For the largest prime `q ≤ n` one would need `q > 2n/3`
(then `A_k^{(s)}` has exactly one `q`-pole, from `ℓ = (q-1)/2`), which needs more than Bertrand;
`q = n - 1` avoids this.  In all cases:
* an *upper* bound `v_q(ρ₀) ≤ -e` — exhibit the `q`-adic principal part of
  `ρ₀ = -∑_{i,k} (i)₄ r_{i,k} A_k^{(i+4)}`;  beware the critical-zero cancellation of GAP 2 step 4,
  which kills the principal part coming from `A_k` for `q > n`;
* *lower* bounds `v_q(Z₇) ≥ -e + 1`, `v_q(Z₉) ≥ -e + 1` — the GAP 2 derivative lemma gives
  `v_q(c_i) ≥ s_res(q) - (6 - i)`.
Everything is about the explicit rationals `ρ₀, Z₇, Z₉`; no 2-adic analysis is needed.

**Alternative routes.**
1. *Lai's dominant term* (proof.md §7): along a subsequence (e.g. `m` such that `40m` has a
   special binary shape) find a unique Leibniz term of `-R_n'''(x + 1/2)` of minimal 2-adic
   valuation (`Stmt_IntegrandTaylor`, `Stmt_Delta`, `Stmt_DeltaFun`), compute its level-`N`
   Riemann sum exactly.  Lai's digit lemma is tied to `n = 2^m - 1`, incompatible with `40 ∣ n` as
   is; a configuration with power-of-2 denominators could be chosen instead (then add a new
   `Config`).
2. *Casoratian / recurrence* (LSZ §4): only works cleanly for a single zeta value; unlikely here.

**Lean hints.** `Nonvanishing_of_LaiSprang`, `frequently_prime_forty_mul_sub_one_gt`,
`Nat.frequently_atTop_prime_and_modEq`, `Filter.frequently_atTop`, `Filter.Frequently.mono`,
`Filter.Frequently.and_eventually`, `padicValRat.mul`, `padicValRat.min_le_padicValRat_add`,
`padicValRat.of_int`, `Rat.num_div_den`, `Rat.cast_injective` (`ℚ → ℚ_[2]`), `HasVolkenborn.unique`.

**Numerical check.** `python/pair_mirror.py`, sections "GAP data" (`S!=0`) and "Stmt_LaiSprangCond";
`python/pair_audit_independent.py`, section E.
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Pair

theorem Nonvanishing_proof (hL1 : Stmt_L1) (hIT : Stmt_IntegrandTaylor) (hD : Stmt_Delta)
    (hDF : Stmt_DeltaFun) (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) (hCI : Stmt_CrudeInt) :
    Stmt_Nonvanishing configE := by
  sorry

end Zeta2.Pair

end
