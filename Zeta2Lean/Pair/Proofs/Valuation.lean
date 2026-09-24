import Zeta2Lean.Pair.Statements

/-!
# GAP 4: 2-adic smallness `v₂(S_n) ≥ 12 n - O(log n)` (proof.md §5 "L3", adapted to shifted factors)

gap: 'valuation' (GAP 4 of the pair programme; **expected routine** — it is a proof obligation of
`Pair/Main.lean`, not a hypothesis).

**Task.** Prove `Stmt_Valuation` from `Stmt_IntegrandTaylor` (pair), `Stmt_Delta` and
`Stmt_DeltaFun` (reused from the `{7,9,11}` project): there are `c : ℝ`, `A : ℕ` such that for every
admissible `(n, h)` and every limit `I` of the Riemann sums of `integrand n h`,
`‖I‖ · 2^{12n} ≤ c (n+1)^A`.  (Unnormalised: `R_n` has no `2^{12n}` prefactor.)
Numerically `12n - v₂(S_n) = 23, 25, 25, 27, 35, 37` for configuration E at
`n = 40, 80, 120, 160, 200, 400`; the proof below gives roughly `A ≈ 13`.

**Informal proof.**
*Product form.* By `Stmt_IntegrandTaylor`, `integrand n h x = -6 [ε³] R_n(x + 1/2 + ε)`, and with
`y = x + 1/2`, `y + 1/2 + u = x + 1 + u`, `y + j = (2x + 2j + 1)/2`:
```
R_n(x + 1/2 + ε) = 2^{6n+6} · (2x + 1 + n + 2ε) · ∏_{f ∈ F} (a_f(x) + ε) · H_x(ε),
F = {(m,u) : u ∈ [-h_m, n+h_m)} (6n factors),  a_{(m,u)}(x) = x + 1 + u,
H_x(ε) = ∏_{j=0}^{n} (2x + 2j + 1 + 2ε)^{-6} = ∑_β 2^β η_β(x) ε^β,
η_β(x) = [δ^β] ∏_{j=0}^{n} (2x + 2j + 1 + δ)^{-6}
```
(`η_β` is an integer polynomial in the `1/(2x+2j+1)`, so it is `ℤ₂`-valued with `Δ(η_β) ≥ 0` —
same proof as `Stmt_DeltaFun.hcoefDelta` of the sibling, with exponent 6 instead of 8).
*Leibniz.* `[ε³]` of the product is a sum over `γ ∈ {0,1}` (ε taken from the linear factor), `β`
(from `H`) and a subset `M ⊆ F`, `|M| = 3 - γ - β` (ε taken from those linear factors):
```
term(γ, β, M)(x) = (γ = 0 ? 2x + 1 + n : 2) · 2^β η_β(x) · ∏_{f ∈ F \ M} a_f(x).
```
*Block products.* In block `m` (length `N_m = n + 2h_m ≤ 2n`: at most one shift is negative and
`∑ h = 0`), removing `r_m = |M ∩ block m| ≤ 3` factors leaves `r_m + 1` runs of consecutive
integers of lengths `L_0 + … + L_{r_m} = N_m - r_m`, and a run `(z)_L = L! · C(z + L - 1, L)`
(generalised binomial).  Legendre/Kummer: `v₂(∏_i L_i!) ≥ v₂(N_m!) - 2 r_m ⌈log₂(N_m + 1)⌉` (the
quotient is a multinomial coefficient with `2 r_m + 1` parts), and `v₂(N_m!) = N_m - s₂(N_m)`.  So
every term is `K · Φ` with an integer constant
`v₂(K) ≥ 6n + 6 + ∑_m (N_m - s₂(N_m) - 2 r_m ⌈log₂(2n+1)⌉) ≥ 12 n + 6 - 12 ⌈log₂(2n+1)⌉`
(`∑_m N_m = 6n`) and a product `Φ` of `ℤ₂`-valued functions: the linear factor (`Δ ≥ 0`),
`η_β` (`Δ ≥ 0`) and at most `6 · 4` generalised binomials `C(x + a, L)`, `L ≤ 2n` (`Δ ≥ -⌊log₂ L⌋`).
*Δ-calculus* (`Stmt_Delta`): `mulAll` (products of `ℤ₂`-valued functions), `smulAll` (the
constant), `sumAll` (finitely many terms), then `riemannAll`: every Riemann sum has
`v₂ ≥ 12n + 6 - 12⌈log₂(2n+1)⌉ - ⌊log₂ 2n⌋ - 1 - v₂(6)`.  Limits preserve the closed bound
(`le_of_tendsto` on `‖·‖`), which gives the claim with `A = 13`, `c = 2^{30}` (say).

**Pitfall (shifted factors).** For `h_m > 0` and small `x` the run `(x + 1 - h_m)_{L}` contains
non-positive integers, so `C(x + a, L)` with `a < 0` is **not** `Nat.choose (x + a) L`.
Recommended fix: expand the generalised binomial by Vandermonde,
`C(x + a, L) = ∑_k C(a, L - k) C(x, k)` with integer coefficients `C(a, ·)` (`Ring.choose`), and use
`Stmt_DeltaFun.binom` with `j = 0` (`Δ(C(x, k)) ≥ -⌊log₂ k⌋`) with `Stmt_Delta.sumAll`/`smulAll`.
(Translating the variable by `max_m h_m` would also make all runs start at `≥ 1`, but it needs a
translation lemma for general `f`; the sibling's `Stmt_Translation` covers only `halfPow`.)

**Lean hints.** `Stmt_Delta` fields `riemannAll`, `sumAll`, `smulAll`, `mulAll`, `monoAll`;
`Stmt_DeltaFun.binom`; `Padic.norm_le_pow_iff_norm_lt_pow_add_one`, `padicValNat.factorial`,
`sub_one_mul_padicValNat_factorial` (Legendre: `v₂(N!) = N - s₂(N)`), `Nat.digits_sum`,
`padicValNat_choose` (Kummer), `Nat.log`, `le_of_tendsto'`, `Filter.Tendsto.norm`,
`Finset.prod_Ico_consecutive`, `Nat.ascFactorial_eq_factorial_mul_choose`, `Ring.choose`,
`Nat.add_choose_eq` (Vandermonde).  Consider proving an intermediate "Leibniz" identity
`integrand n h x = ∑_{γ,β,M} (explicit term)` in this file first (the sibling's `Stmt_Leibniz` is
the model), then the per-term Δ bound, then the sum.

**Numerical check.** `python/pair_mirror.py`, section "Stmt_Valuation (GAP 4)":
`max (12n - v₂(S_n))/log₂(n+1) ≤ 5.7` over all tested admissible `(n, h)`.
-/

open Filter Topology Finset PowerSeries

noncomputable section

namespace Zeta2.Pair

theorem Valuation_proof (hIT : Stmt_IntegrandTaylor) (hD : Stmt_Delta) (hDF : Stmt_DeltaFun) :
    Stmt_Valuation := by
  sorry

end Zeta2.Pair

end
