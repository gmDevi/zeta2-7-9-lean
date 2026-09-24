import Zeta2Lean.Pair.Statements

/-!
# GAP 1 (growth): exponential decay of `ρ₀, Z₇, Z₉` for configuration E

gap: 'growth' (open research problem; hypothesis of the main theorem).

**Task.** Prove `Stmt_Growth configE gE`, i.e. for every `ε > 0`, eventually in `m` (`n = 40 m`,
`h = m · (-17, 1, 2, 3, 5, 6)`):
  `|ρ₀|, |Z₇|, |Z₉| ≤ exp((-0.72 + ε) n)`.
Any `g` with `g + δ < 12 log 2 = 8.3178` works together with a denominator rate `δ`
(`Pair/Main.lean`, `zeta2_7_9_not_both_rational_of_gaps`); with the residue-level provable
`δ ≈ 8.91` one needs `g < -0.59`.  Polynomial factors are irrelevant (absorbed by `ε`).  The
hypotheses `Stmt_PF`, `Stmt_CoeffVanish` are available; ask the architect for more.

**Numerical status** (exact, unnormalised; `raw/n = log max(|ρ₀|, |Z₇|, |Z₉|)/n`):
`-0.769 (n=40), -0.818 (80), -0.827 (120), -0.817 (160), -0.820 (200), -0.807 (400),
-0.8046 (640), -0.7975 (800)`; slow drift upwards, fits `≈ -0.786`.  The naive bound
`max_k log|r_{6,k}|/n` (top residues, Stirling) is `+0.77` at `k/n ≈ 0.35` — about `1.6` nats per
`n` of cancellation in the sums over `k` must be proved.  The boundary formula `∑_m c(η_m)`
(`c(η) = η log η + (1+η) log(1+η) - 2η` for `η ≥ 0`, `(1+η) log(1+η) + η log(-η) - 2η` for
`η < 0`) predicts `-0.488` for E but is **not** what happens (it does describe configurations with a
zero shift, e.g. A: `-0.366` vs measured `-0.397` at `n = 400`).

**Architect's saddle-point conjecture (new, numerical; `scratchpad/pair79/architect/
saddle_growth.py`).**  Let `F(z) = z log z - z` (principal branch) and, with `η = h/n`,
```
φ(τ) = ∑_m [F(τ + 1 + η_m) - F(τ - η_m)] - 6 [F(τ + 1) - F(τ)]      (|R_n(nτ)| ≈ e^{n Re φ(τ)}).
```
The points with `e^{φ'(τ)} = 1` are the roots of the degree-9 polynomial
`∏_m (τ + 1 + η_m) τ^6 - ∏_m (τ - η_m) (τ + 1)^6`.  For E they are `τ = -1/2` (`φ' = 0`,
`Re φ = +0.652`: the naive interior bound), real `τ = 0.025030` (`φ' = -4πi`, value `-0.80049`),
`τ = 0.046326` (`-0.85201`), and the complex pair `τ* = 0.069590 ± 0.031280 i` with `φ' = ∓2πi`,
where
```
Re [φ(τ*) + 2πi τ*] = -0.58474 - 2π · 0.031280 = -0.78128 ,
```
(plus mirror images under `τ ↦ -1 - τ`).  **Conjecture: `g_E = -0.78128…`** = the maximum of
`Re[φ(τ*) - 2πi k τ*]` (`φ'(τ*) = 2πik`) over the points `τ*` to the right of the pole interval
(`Re τ* > 0`), here attained at the complex saddle of `φ(τ) + 2πiτ`; this matches the fitted limit
`-0.786`.  Cross-check on the `{7,9,11}` configuration D (`a = 8`,
`η = (-0.4,-0.4,0.05,0.1,0.1,0.15,0.2,0.2)`): the same recipe gives `-1.1808` (complex saddle
`0.1208 + 0.0680 i`), measured `-1.29, -1.26, -1.24, -1.24, -1.22` at `n = 120 … 650` (rising).
Points inside the pole interval (e.g. `τ = -1/2`, value `+0.652`; for D also `τ = -0.3196`) are the
naive residue bounds and must be excluded.  Configurations with a zero shift are instead governed
by the boundary formula above.  The
`2πiτ` term is the signature of a kernel `e^{±2πit}` (`π cot πt`, `π/ sin πt`, polygamma
differences) in a contour-integral representation — see below.

**Suggested routes.**
1. *Contour integrals + saddle points.*  From
   `∑_i (i)₄ r_{i,k} x^{-(i+4)} = 24 Res_{t=-k} R(t) (x_c - t)^{-5}`
   (`x = ℓ + 1/2 = x_c + k`, `x_c = 1/2 - c`, `c = k - ℓ`):
   `ρ₀ = -24 ∑_{c=1}^{n} ∑_{k=c}^{n} Res_{t=-k} [R_n(t) (1/2 - c - t)^{-5}]
       = 24 ∑_{c=1}^{n} (1/2πi) ∫_{Re t = -c + 1/4} R_n(t) (1/2 - c - t)^{-5} dt`
   (close to the left; `R_n(t)(…)^{-5} = O(|t|^{-10})`).  Summing the kernels over `c` produces a
   polygamma-type kernel whose behaviour off the real axis is `e^{±2πit}`; deform through `τ*`.
   Similarly `c_i = ∑_k Res_{t=-k} R_n(t) (t+k)^{i-1}` (use kernels `(π cot πt)^{(j)}`, i.e.
   `∑_{k ∈ ℤ} (t+k)^{-j-1}`, to express the sums of residues as one contour integral).  The
   critical zeros (`R_n` vanishes to order `≥ 5` at `t = -1/2 - c`, `0 ≤ c < n`) let one switch
   between `∑_{k ≥ c}` and `-∑_{k < c}`.
2. *Multiple-sum (Andrews/Whipple) representation* with positive terms, as in LSZ Lemma 5.2 /
   proof.md §4.3 for the unshifted case (the shifted family is still very-well-poised).
3. *Recurrence in `m`* (creative telescoping) + Poincaré–Perron, identifying the dominant
   characteristic root with `e^{40 g}`; the order may be large.
4. *Archimedean analogue*: `∑_{ν ≥ 0} R_n'''(ν + 1/2)` is a very-well-poised series whose
   coefficients of `ζ(6), ζ(8)` are, up to `(2^s - 1)`-factors, the same `c₃, c₅` (Rhin–Viola /
   Zudilin saddle-point technology applies verbatim to `c₃, c₅`; `ρ₀` needs route 1).

**Lean hints (for the final formal step).** `Real.exp_le_exp`, `Finset.abs_sum_le_sum_abs`,
`Real.exp_sum`, `Real.log_le_sub_one_of_pos`, Stirling (`Stirling.le_factorial_stirling`,
`Stirling.factorial_isEquivalent_stirling`), `Nat.choose_le_pow`, `Real.rpow_natCast`.
Complex-analytic saddle-point bounds are not in Mathlib in usable form; a real-variable proof
(majorants, positivity of a multiple-sum representation) is far easier to formalise if one exists.

**Numerical check.** `python/pair_mirror.py`, section "GAP data for configuration E" (column
`raw/n`).
-/

open Filter Topology Finset

noncomputable section

namespace Zeta2.Pair

theorem Growth_proof (hPF : Stmt_PF) (hV : Stmt_CoeffVanish) : Stmt_Growth configE gE := by
  sorry

end Zeta2.Pair

end
