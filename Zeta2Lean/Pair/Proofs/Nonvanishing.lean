import Zeta2Lean.Pair.Statements

/-!
# GAP 3 (nonvanishing): `S_n ≠ 0` infinitely often along configuration E

gap: 'nonvanishing' (open; hypothesis of the main theorem).

**Task.** Prove `Stmt_Nonvanishing configE`: if `ζ₂(7)` and `ζ₂(9)` are both rational, then for
infinitely many `m` every limit `I` of the Riemann sums of `integrand (40m) (m · hE)` is non-zero.
(The rationality hypotheses may be used; an unconditional proof simply ignores them.)

**Numerical status.** `S_n ≠ 0` at every tested `n` (`n ≤ 800`; `v₂(S_n) - 12n = -23 … -39`).

**Recommended route: the Lai–Sprang `ℓ(n)`-adic condition** (Lai–Sprang arXiv:2306.10393,
Lemma 2.2), packaged as `Stmt_LaiSprangCond configE` (`Pair/Statements.lean`), which implies this
statement by the routine lemma `Nonvanishing_of_LaiSprang` (`Pair/Proofs/NonvanishingLS.lean`):
it suffices to find, for every bound `B` and infinitely many `m`, a prime `q > B` with `ρ₀ ≠ 0`,
`v_q(ρ₀) < v_q(Z₇)` and `v_q(ρ₀) < v_q(Z₉)`.  Numerically this holds for **every** prime
`q ∈ (√n, n]` at `n = 120, 200, 400` (26, 40, 70 primes), always with
`v_q(Z₇) - v_q(ρ₀) ≥ 7` and `v_q(Z₉) - v_q(ρ₀) ≥ 9`, `v_q(ρ₀) ∈ [-11, -5]`
(`scratchpad/pair79/architect/laisprang_check.out`).  A natural choice is the largest prime
`q ≤ n` (then `q > n/2` for large `n`, `v_q(d_n) = 1`, and `A_k^{(s)}` has exactly one `q`-pole,
from `ℓ = (q-1)/2`).  What must be proved at such `q`:
* an *upper* bound `v_q(ρ₀) ≤ -e` — exhibit the `q`-adic principal part of
  `ρ₀ = -∑_{i,k} (i)₄ r_{i,k} A_k^{(i+4)}`: only the term `ℓ = (q-1)/2` of `A_k^{(i+4)}`
  (for `k > ℓ`) carries `q^{-(i+4)}`, so the principal part is
  `-∑_i (i)₄ (2/q)^{i+4} ∑_{k > (q-1)/2} r_{i,k}` modulo lower-order terms; show one of these
  partial sums is a `q`-unit multiple of the expected power (Legendre on `r_{6,k} = G_k(0)`);
  beware the critical-zero cancellation of GAP 2 step 4, which kills exactly this principal part
  for `q > n`;
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

**Lean hints.** `Filter.frequently_atTop`, `Filter.Frequently.mono`, `padicValRat.mul`,
`padicValRat.min_le_padicValRat_add`, `padicValRat.of_int`, `Rat.num_div_den`, `Rat.cast_injective`
(`ℚ → ℚ_[2]`), `HasVolkenborn.unique`.

**Numerical check.** `python/pair_mirror.py`, sections "GAP data" (`S!=0`) and "Stmt_LaiSprangCond".
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Pair

theorem Nonvanishing_proof (hL1 : Stmt_L1) (hIT : Stmt_IntegrandTaylor) (hD : Stmt_Delta)
    (hDF : Stmt_DeltaFun) : Stmt_Nonvanishing configE := by
  sorry

end Zeta2.Pair

end
