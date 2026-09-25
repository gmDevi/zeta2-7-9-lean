# At least one of ζ₂(7), ζ₂(9) is irrational — assembled proof (configuration E)

> **Editorial note (2026-09-25, for this repository).** This is the informal proof of the theorem
> formalised in this repository, as assembled on 2026-09-24 by the AI research session that
> produced it (`formalization.yaml`, `automation`, describes the process). No human expert has
> refereed it. The file paths it mentions (`pair79/...`, `lai2/...`, `assembly/...`) are in that
> session's working directory and are not part of this repository. Apart from this note, the
> novelty remarks in §0 and §11 A3 and a note in §12, the text is unchanged. The Lean proof
> follows the minimal route of §8 with weaker constants (growth rate −0.72 instead of −0.78127,
> odd denominators e^{8.97n+o(n)} instead of e^{8.9099n+o(n)}), its own kernel-checked
> certificates, and the opposite sign convention S_n = −∫ R_n'''(t+½) dt; `README.md` ("The proof
> in Lean") describes it and lists the differences.

Track `pair79/assembly`, 2026-09-24. This is a raw working document for another model or a referee.

It assembles the four gap proofs of the pair79 tracks into one proof: growth (GAP 1), denominators (GAP 2),
nonvanishing (GAP 3) and valuation (GAP 4). Each was adversarially re-derived by an independent verifier. The assembled
proof uses **one** family, **one** configuration and **one** subsequence of n. It then referees itself (§11).

Every step carries one of the labels of the (8,3) draft `lai2/prove-7-9-11/proof.md`:
- **PROVED**: the complete argument is given here, modulo the published facts (P1)–(P9) of §2.
- **PROVED (computer-assisted)**: the complete argument is given here, and its finite verification is a named exact or
  interval computation.
- **PROVED + NUMERICAL**: the complete argument is given here, and it was also checked on exact data.
- **NUMERICAL**: evidence only.

All paths below are relative to the scratchpad directory. Source tracks:
- `pair79/growth/proof.md` (GAP 1), verified in `pair79/verify-growth/`;
- `pair79/denominators/proof.md` (GAP 2), verified in `pair79/verify-denominators/`;
- `pair79/nonvanishing/proof.md` (GAP 3), verified in `pair79/verify-nonvanishing/`;
- `pair79/valuation/proof.md` (GAP 4), verified in `pair79/verify-valuation/`;
- this track's own cross-checks are in `pair79/assembly/`.

---------------------------------------------------------------------------------------------------

## 0. Statement, status and the total margin

**Theorem.** Let ζ₂(s) := L₂(s, ω^{1−s}) be the Kubota–Leopoldt 2-adic zeta value [LSZ, Def. 2.7], so ζ₂(even) = 0.
At least one of the two 2-adic numbers ζ₂(7), ζ₂(9) is irrational.

The definitions of Coleman and Furusho differ from this one by the Euler factor (1 − 2^{−s})^{−1}. That factor is a
nonzero rational number, so the statement does not depend on the normalisation.

**Context.**
- Lai, IJNT 21 (2025), Thm 1.1 with s = 3, proves: at least one of ζ₂(7), ζ₂(9), ζ₂(11), ζ₂(13) is irrational.
- The project's (8,3) draft proves the same for {ζ₂(7), ζ₂(9), ζ₂(11)}.
- Lai–Sprang–Zudilin (LSZ) prove ζ₂(5) ∉ ℚ.
- The pair statement here would strengthen the first two.

**The objects** (fixed once and for all; §3):
- **Family.** R_n(t) = (2t+n)·∏_{m=1}^{6}(t+½−h_m)_{n+2h_m} / (t)_{n+1}^6.
- **Configuration E.** h = (n/40)·(−17, 1, 2, 3, 5, 6), with 40 | n.
- **Linear forms.** S_n = ∫_{ℤ₂} R_n'''(t+½) dt = ρ₀ + Z₇ζ₂(7) + Z₉ζ₂(9).
- **Subsequence.** I := {n : 40 | n, n − 1 prime, n ≠ 91080}. It is infinite by Dirichlet, since it is the set of
  primes ≡ 39 (mod 40) shifted by 1, minus one point.

| step | content | status | source |
|---|---|---|---|
| L0 | construction; degree −5; critical zeros of order ≥ 5; symmetry R_n(−n−t) = −R_n(t) | **PROVED** | §3 (all tracks) |
| L1 | S_n = ρ₀ + Z₇ζ₂(7) + Z₉ζ₂(9), Z₇ = −46080c₃, Z₉ = −860160c₅; c₁ = c₂ = c₄ = c₆ = 0 | **PROVED + NUMERICAL** | §3; valuation §7.1, nonvanishing §2 |
| L2 | odd common denominator D_n: no prime > n; small primes O(√n); large primes ≤ residue level. log D_n ≤ (10 − R⁽⁰⁾)n + o(n) with R⁽⁰⁾ = 1.0901241927613 | **PROVED (computer-assisted)** for the value of R⁽⁰⁾, which has three independent implementations | §4.1–4.5; denominators §§1–5, 8 |
| L2⁺ | sharper: R⁽²⁾ = R⁽⁰⁾ + 1/5 (second order); R_E = 1.4517049996220 (third order, row cancellation). **Not needed for the Theorem.** | **PROVED (computer-assisted)** | §4.6; denominators §§3–8 |
| L3 | v₂(S_n) ≥ 12n + 9 − σ_n − 4λ_n ≥ 12n − 1 − 10·log₂(1.3n) for every n ≡ 0 (mod 40) | **PROVED + NUMERICAL** | §5; valuation |
| L4 | max(\|ρ₀\|, \|Z₇\|, \|Z₉\|) ≤ 1.56·10¹²·n^{−4}·e^{−0.7812n} for n ≡ 0 (mod 40), n ≥ 2000; exponent −0.78127 for n ≥ 10⁴ | **PROVED (computer-assisted)** | §6; growth |
| L5 | for n ∈ I and ℓ = n − 1: v_ℓ(ρ₀) = −9, v_ℓ(Z₇) ≥ −3, v_ℓ(Z₉) ≥ −1 | **PROVED + NUMERICAL** | §7; nonvanishing |
| L6 | conclusion along I; total margin | **PROVED** (given L1–L5) | §8 |

**The total margin** (§8). For n ∈ I, let D_n be the least odd positive integer such that D_nρ₀, D_nZ₇, D_nZ₉ ∈ ℤ[½].
Choose e_n ≥ 0 with a_{n,·} := 2^{e_n}D_n·(ρ₀, Z₇, Z₉) ∈ ℤ³, and put
L_n := a_{n,0} + a_{n,1}ζ₂(7) + a_{n,2}ζ₂(9) = 2^{e_n}D_nS_n. Then

  limsup_{n∈I} (1/n)·log( max_i |a_{n,i}| · |L_n|₂ ) ≤ 10 − 12 log 2 + g − R,   with g = −0.78127 (L4).

| denominators used | R | total margin |
|---|---|---|
| **all proved ingredients (third order, L2⁺)** | **1.451704999622** | **−0.5507412** |
| second order only (L2⁺ without the row cancellation) | 1.290124192761 | −0.3891604 |
| residue level only (L2; the minimal route used in §8) | 1.090124192761 | −0.1891604 |

Break-even points:
- At g = −0.78127, the margin stays negative as long as R > 0.9009638, i.e. log D_n ≤ (9.0990362 − ε)n.
- At R = R_E, it stays negative as long as g < −0.2305288.
- The saddle value g* = −0.7812761397, which is the growth rate's limit numerically but is not proved to be the limit
  (§6.6), would give −0.5507473.

**Assembled total margin: −0.5507 per n** (i.e. max|a_{n,i}|·|L_n|₂ ≤ e^{−0.5507n+o(n)} along I). The Theorem itself
only needs the residue-level route, which has margin −0.189 per n.

**Honest caveats** (full referee report in §11).
1. Nothing here has been refereed by a human. Four long new arguments are combined.
2. Two steps are computer-assisted:
   - three interval-arithmetic inequalities for a saddle-point landscape (L4). They were certified twice with
     mpmath.iv. This assembly certified all of them a third time, standard and sharp versions, at full strength. The
     third run uses its own rational enclosures of log, atan, π and 1/e, a different bounding method, and no floating
     point;
   - the exact evaluation of the savings constant R (L2), done by three independent implementations.
3. The o(n) in L2 is ineffective, since it comes from the PNT. The argument therefore gives no explicit n₀.
4. Novelty: the literature search recorded in `formalization.yaml` (2026-09-24) found no prior statement of this
   result or of the {7, 9, 11} result; unrefereed drafts by C. D. Long (August 2026) claim stronger results that would
   imply both. The search was not exhaustive (§11 A3).

---------------------------------------------------------------------------------------------------

## 1. Where each ingredient comes from

* **The family.** It extends the LSZ ζ₂(5) family 2^{8n}(2t+n)(t+½)_n^4/(t)_{n+1}^4, which is (a,j) = (4,1), to
  (a,j) = (6,3). The numerator Pochhammers are replaced by the shifted, "well-poised" (Rhin–Viola-type) blocks
  (t+½−h)_{n+2h}. Each block is symmetric under t ↦ −n−t for **every** h, so the LSZ parity mechanism survives.
  The shift vector is chosen for three reasons:
  - Σh = 0 keeps deg R = −5 and the 2-adic rate 12 log 2.
  - Five shifts h_m ≥ n/40 > 0 give **critical zeros**: R vanishes to order ≥ 5 = j+2 at every half-integer in
    (−n−n/40, n/40). This removes all primes q > n from the denominators (L2(a)), and it lets the growth contour cross
    the real axis (L4).
  - One strongly negative shift, h₁ = −17n/40, produces prime-selective denominator savings (R > 0).
* **L1.** This is the LSZ Lemma 3.3 mechanism: partial fractions, the Volkenborn translation formula and
  J_s = s·2^{s+1}ζ₂(s+1). It is identical to (8,3)-draft L1.
* **L2.** The Lai–Yu/Zudilin building blocks do not apply to factors with h < 0; the verifier found prime exponents
  a+j+2 = 11. The denominator track therefore works directly with the local linear factors at each pole. It uses:
  - a Legendre count at each pole;
  - a first-order Taylor lemma;
  - the critical zeros, to remove primes q > n.
  The refinements L2⁺ add a second-order Taylor lemma, Lai's root trick applied per anti-diagonal ([Lai] Lemma 4.6),
  and a Wilson-type translation plus reflection. Together these give a "row cancellation" that replaces the Andrews
  transformation used in LSZ Lemma 5.3.
* **L3.** Sprang's and Lai's Δ-calculus ([Lai] Def. 2.3, Lemmas 2.4–2.5), plus a lemma on derivatives of binomial
  coefficients.
* **L4.** New. Each coefficient is written as a Barnes-type contour integral against a periodic kernel. The kernel has
  poles only at half-integers, which is allowed because of the critical zeros. The size is then bounded by a saddle
  point, and three landscape inequalities are certified by interval arithmetic. The archimedean template is
  Zudilin (JTNB 2004, §2).
* **L5.** The Lai–Sprang ℓ(n)-adic idea ([LS] Lemma 2.2) with ℓ = n − 1. It replaces Lai's 2-adic dominant-term method,
  which has no unique dominant term for this family.
* **L6.** The elementary criterion [Lai, Lemma 2.1], with the nonvanishing built in, written out in full in §8.

---------------------------------------------------------------------------------------------------

## 2. Notation and cited tools

**Notation.**
- (x)_k is the rising factorial, C(x,k) = x(x−1)⋯(x−k+1)/k! the binomial coefficient, s₂(N) the binary digit sum, and
  [ε^λ]F the Taylor coefficient at ε = 0.
- v_q is the q-adic valuation on ℚ (and on ℚ₂ for q = 2), and ℤ_(q) := {x ∈ ℚ : v_q(x) ≥ 0}.
- H_m := Σ_{j≤m} 1/j.
- θ(x) := Σ_{p≤x} log p.
- For k ≥ 1, k₋ denotes k with its leading binary digit deleted.

**Cited tools.**
- **(P1) Volkenborn integral** [Robert, *A Course in p-adic Analysis*, GTM 198, Ch. 5; LSZ §2.2].
  - Definition: ∫_{ℤ₂} f(t)dt := lim_N 2^{−N}Σ_{x<2^N} f(x).
  - It exists for f ∈ S¹(ℤ₂,ℚ₂), in particular for every rational function with no pole in ℤ₂ [Robert p. 264], and it
    is ℚ₂-linear.
  - Translation [Robert §5.3 Prop. 2, p. 265; LSZ Lemma 2.4; Lai Lemma 2.2]: for k ≥ 1,
    ∫f(t+k)dt = ∫f(t)dt + Σ_{l=0}^{k−1} f'(l).
- **(P2) 2-adic zeta values** [LSZ Lemma 2.8 and §2.3]. For s ≥ 1, J_s := ∫_{ℤ₂}(t+½)^{−s}dt = s·2^{s+1}·ζ₂(s+1), and
  ζ₂(2k) = 0. Hence J_s = 0 for odd s. (LSZ Lemma 2.8, checked in `lai2/prove-7-9-11/lsz.txt`, states
  (1/(s−1))∫(t+½)^{1−s}dt = 2^sζ₂(s).)
- **(P3) Δ-calculus** [Lai Def. 2.3, Lemmas 2.4 and 2.5; LSZ Lemmas 2.5 and 2.6]. The facts (D1)–(D4) used are
  re-proved in §5.
- **(P4) Elementary number theory.**
  - Legendre: v_q(m!) = Σ_{e≥1}⌊m/q^e⌋, and v₂(N!) = N − s₂(N).
  - Wilson: (q−1)! ≡ −1 (mod q).
  - Among any q^e consecutive odd integers, exactly one is divisible by q^e (q odd).
- **(P5) Prime number theorem** θ(x) = x + o(x), and Rosser–Schoenfeld θ(x) < 1.01624x for x > 0.
- **(P6) Dirichlet's theorem.** There are infinitely many primes ≡ 39 (mod 40).
- **(P7) Complex analysis** [Ahlfors, *Complex Analysis*, 3rd ed., Ch. 4 §5.1 (residue theorem), Ch. 4 §6 (maximum
  principle for harmonic functions)].
- **(P8) Rigorous computation.**
  - Interval arithmetic with outward rounding [mpmath 1.3.0, module `mpmath.iv`].
  - Exact rational arithmetic (Python `fractions`).
  - A second, independent certification of L4's inequalities on exact rational boxes (harmonic Taylor bounds; point
    values again from mpmath.iv).
  - A third certification, written for this assembly (`assembly/cert3.py`, `cert3b.py`). It uses no mpmath and no
    floating point: it has its own rational series enclosures of log, atan, π and 1/e, with explicit remainders.
- **(P9) Digamma.** ψ(z) − ψ(w) = Σ_{j≥0}(1/(j+w) − 1/(j+z)).

The irrationality criterion ([Lai] Lemma 2.1 and its ℓ(n)-adic variant [LS] Lemma 2.2) is proved in the form needed in
§8, so it is not cited.

References:
- [Lai] L. Lai, *On the irrationality of certain 2-adic zeta values*, IJNT 21 (2025) 207–235, arXiv:2304.00816.
- [LS] L. Lai, J. Sprang, *Many p-adic odd zeta values are irrational*, arXiv:2306.10393v2.
- [LSZ] L. Lai, J. Sprang, W. Zudilin, *A note on the irrationality of ζ₂(5)*, arXiv:2505.05005.
- [Zud] W. Zudilin, *Arithmetic of linear forms involving odd zeta values*, JTNB 16 (2004) 251–291.

---------------------------------------------------------------------------------------------------

## 3. The construction, L0 and L1

### 3.1 Configuration E

Fix n ∈ 40ℤ_{>0}. Put

  h = (h₁,…,h₆) := (n/40)·(−17, 1, 2, 3, 5, 6) ∈ ℤ⁶,   η := h/n = (−0.425, 0.025, 0.05, 0.075, 0.125, 0.15).

Then:
- Σ_m h_m = 0;
- N_m := n + 2h_m = n·(3/20, 21/20, 11/10, 23/20, 5/4, 13/10) > 0;
- the largest shift is h_max = h₆ = 3n/20, so N* := max N_m = 13n/10.

Put C_m := [−h_m, n+h_m−1] ∩ ℤ. Then |C_m| = N_m, and (t+½−h_m)_{N_m} = ∏_{c∈C_m}(t+½+c). Moreover
C₁ = [17n/40, 23n/40−1], and C_m ⊇ [−n/40, n−1+n/40] for m ≥ 2. Define

  R_n(t) := (2t+n) · ∏_{m=1}^{6} ∏_{c∈C_m}(t+½+c) / ∏_{k=0}^{n}(t+k)⁶ = Σ_{i=1}^{6} Σ_{k=0}^{n} r_{i,k}(t+k)^{−i},   c_i := Σ_k r_{i,k}.

Also put G_k(ε) := ε⁶R_n(−k+ε), and let PP_k(t) := Σ_i r_{i,k}(t+k)^{−i} be the principal part at −k.

### 3.2 Lemma 0 (basic properties) — PROVED

(a) **Degree and partial fractions.**
- deg R_n = 1 + ΣN_m − 6(n+1) = −5.
- The poles are the integers −k (0 ≤ k ≤ n), of order ≤ 6. The zeros of the numerator are half-integers, except the
  zero −n/2 of 2t+n, which lowers the pole at k = n/2 to order 5. So the partial-fraction expansion displayed in §3.1
  holds exactly, with r_{i,k} ∈ ℚ and no polynomial part.
- r_{6−λ,k} = [ε^λ]G_k(ε) for 0 ≤ λ ≤ 5, where

  G_k(ε) = (n−2k+2ε) · ∏_m ∏_{c∈C_m}(ε + c−k+½) · ∏_{j∈[0,n], j≠k}(ε + j−k)^{−6}.        (3.1)

- For k = n/2 we write G_k = 2ε·H_k, with H_k holomorphic at 0, so that r_{6−λ,n/2} = 2[ε^{λ−1}]H_{n/2}.

(b) **Critical zeros.** For c ∈ ℤ, R_n has no pole at −½−c. It vanishes there to order μ(c) := #{m : c ∈ C_m}. Since
C_m ⊇ [−n/40, n−1+n/40] for the five m ≥ 2:

  **μ(c) ≥ 5 for −n/40 ≤ c ≤ n−1+n/40**, i.e. ord_x R_n ≥ 5 at every half-integer x with −n−n/40 < x < n/40.

Moreover μ(n/2−1) = μ(n/2) = 6, because C₁ ∋ n/2−1, n/2 (as 3n/40 ≥ 1).

(c) **Symmetry.** R_n(−n−t) = −R_n(t). Indeed:
- c ↦ n−1−c maps each C_m onto itself, and −n−t+½+c = −(t+½+(n−1−c)); the total sign is (−1)^{ΣN_m} = (−1)^{6n} = 1.
- The denominator gives ((−1)^{n+1})⁶ = 1.
- 2(−n−t)+n = −(2t+n).

Comparing partial fractions gives r_{i,n−k} = (−1)^{i+1}r_{i,k}, hence **c_i = 0 for even i**, and G_{n−k}(ε) = −G_k(−ε).
Differentiating PP_{n−k}(t) = −PP_k(−n−t) four times gives

  PP_{n−k}^{(4)}(t) = −PP_k^{(4)}(−n−t).        (3.2)

(d) **c₁ = 0**: c₁ = lim_{t→∞} tR_n(t) = 0, because deg R_n ≤ −2.

(e) **Real coefficients**: R_n(t̄) = conj R_n(t).

### 3.3 Lemma 1 (linear form) — PROVED + NUMERICAL

R_n(t+½) has no pole in ℤ₂: the poles −½−k have |·|₂ = 2. So S_n := ∫_{ℤ₂}R_n'''(t+½)dt is defined (P1), and

  S_n = ρ₀ + Z₇ζ₂(7) + Z₉ζ₂(9),   Z₇ := −(3)₄2⁷c₃ = −46080c₃,   Z₉ := −(5)₄2⁹c₅ = −860160c₅,

  ρ₀ := Σ_{i=1}^{6}Σ_{k=1}^{n}(i)₄r_{i,k}A_k^{(i+4)} = Σ_{k=1}^{n}Σ_{l=0}^{k−1}X(k,l),   A_k^{(s)} := Σ_{l=0}^{k−1}(l+½)^{−s},

  X(k,l) := Σ_{i=1}^{6}(i)₄ r_{i,k}(l+½)^{−(i+4)} = PP_k^{(4)}(l+½−k) = 24·[ε⁵] G_k(ε)·(l+½−ε)^{−5}.        (3.3)

*Proof.*
1. By partial fractions, R_n''' = −Σ(i)₃r_{i,k}(t+k)^{−i−3}.
2. By (P1) with f = (t+½)^{−s}, since f'(l) = −s(l+½)^{−s−1}, we get ∫(t+k+½)^{−s}dt = J_s − s·A_k^{(s+1)}.
3. Hence S_n = −Σ_i(i)₃c_iJ_{i+3} + Σ_{i,k}(i)₄r_{i,k}A_k^{(i+4)} = −Σ_i(i)₄2^{i+4}c_iζ₂(i+4) + ρ₀, by (P2).
4. c₁ = 0 by Lemma 0(d). For even i the terms vanish by Lemma 0(c), and independently because ζ₂(even) = 0.
5. The last identity in (3.3) follows from 24(x−ε)^{−5} = Σ_{i≥1}(i)₄x^{−(i+4)}ε^{i−1}. ∎

*Remarks.*
- The sign convention S_n = +∫ is used by all four tracks. The (8,3) draft uses −∫, which is irrelevant for everything
  below.
- The constants 46080 = 2¹⁰·3²·5, 860160 = 2¹³·3·5·7 and (i)₄ ∈ {24, 120, 360, 840, 1680, 3024} have only the prime
  factors 2, 3, 5, 7.

*Numerical confirmation.*
- Seven independent exact partial-fraction engines agree on ρ₀, c₃, c₅ wherever they overlap:
  - lfam (explorer) and veng (verifier of smaller-sets);
  - deng (denominators) and xeng (its verifier);
  - vexact (growth verifier);
  - nv_indep (nonvanishing) and vx_exact (its verifier).
- Two further evaluators compute S_n itself directly from the Volkenborn definition, with no partial fractions:
  g4lib's Mahler-series evaluator (valuation track) and vb.py's Bernoulli-number evaluator (its verifier). Against
  them, the identity S_n = ρ₀ + Z₇ζ₂(7) + Z₉ζ₂(9) was checked:
  - modulo 2^{v₂(S)+60} at n = 30, 40, 41, 80 (Mahler series);
  - modulo 2^{449..1529} at n = 30, 40, 41, 80, 120 (Bernoulli numbers, with ζ₂ computed two ways).
- c₁ = c₂ = c₄ = c₆ = 0 at every computed n.


---------------------------------------------------------------------------------------------------

## 4. L2 — the odd common denominator D_n (GAP 2)

Throughout this section, D_n is the least positive **odd** integer with D_nρ₀, D_nZ₇, D_nZ₉ ∈ ℤ[½]. The power of 2 is
irrelevant for the criterion, because it cancels exactly (§8). Fix an odd prime q.

§§4.1–4.5 give the **residue-level** bound, which is all the Theorem needs. §4.6 records the sharper second- and
third-order bounds; they only improve the margin.

### 4.1 Local data at a pole

Write G_k(ε) = G_k(0)·Π_k(ε), with

  Π_k(ε) = ∏_{β∈B_k}(1+ε/β)^{e_β},

where B_k is the multiset of the linear factors of (3.1):
- the numerator values β = c−k+½ (c ∈ C_m, all m), with e_β = +1;
- the δ-value β = (n−2k)/2, with e = +1, for k ≠ n/2;
- the pole values β = j−k (j ∈ [0,n], j ≠ k), with e = −6.

For k = n/2 use H_{n/2} and omit the δ-value. Every β lies in ½ℤ∖{0}, so v_q(β) ≥ 0. Put

  s_k := v_q(G_k(0)) for k ≠ n/2,   s_{n/2} := v_q(H_{n/2}(0)).

**Lemma D1 (Legendre form). PROVED.**

  s_k = Σ_m v_q(∏_{c∈C_m}(2(c−k)+1)) + [k≠n/2]·v_q(n−2k) − 6(v_q(k!) + v_q((n−k)!)),

and **s_k ≥ v_q(K_n)**, where K_n := ∏_m N_m!/(n!)⁶.

*Proof.*
- The identity: ∏_{j≠k}|j−k| = k!(n−k)!, and the powers of 2 do not matter since q is odd.
- The inequality:
  - The N_m numbers 2(c−k)+1, c ∈ C_m, are consecutive odd integers. By (P4), their product has v_q ≥ Σ_e⌊N_m/q^e⌋ = v_q(N_m!).
  - Also v_q(k!) + v_q((n−k)!) ≤ v_q(n!).
  - The δ-term is ≥ 0. ∎

**Lemma D2 (first-order Taylor bound). PROVED.** Let Π(ε) = ∏_β(1+ε/β)^{e_β} with v_q(β) ≥ 0 and e_β ∈ ℤ. Then
v_q([ε^λ]Π) ≥ −Top_λ, where

  Top_λ := max{Σ_β j_β v_q(β) : Σ j_β = λ, j_β ≥ 0, and j_β ≤ e_β whenever e_β ≥ 0}.

In particular:
- Top_λ ≤ λ·max_β v_q(β).
- Suppose every β with v_q(β) > 0 has v_q(β) = 1 and e_β = +1, and there are s such factors (with multiplicity).
  Then Top_λ ≤ min(λ, s).

*Proof.* [ε^λ]Π = Σ_{Σj_β=λ} ∏_β C(e_β, j_β)β^{−j_β}. Here C(e, j) ∈ ℤ, and C(e, j) = 0 for 0 ≤ e < j. ∎

### 4.2 Theorem D (every n ≡ 0 mod 40, every odd prime q) — PROVED + NUMERICAL

(a) If q > n, then v_q(D_n) = 0.

(b) If q² ≤ 2.3n − 1, then v_q(D_n) ≤ 5⌊log_q 1.3n⌋ + 5⌊log_q 2n⌋ + 5⌊log_q 2.3n⌋ ≤ 15·log_q(3n).

(c) If √(2.3n−1) < q ≤ n, then

  v_q(D_n) ≤ E_q^{res} := max(0, 10 − min_{k≠n/2} s_k, 9 − s_{n/2}) ≤ 15.

*Proof of (c).* Call such q **large**. Every β ∈ B_k satisfies |2β| ≤ 2(n+h_max) − 1 = 2.3n − 1 < q², and every l+½
with 0 ≤ l ≤ n−1 satisfies |2l+1| ≤ 2n−1 < q². So all these valuations are 0 or 1.
1. By Lemma D2 with Top_λ ≤ λ: v_q(r_{6−λ,k}) ≥ s_k − λ for k ≠ n/2, and v_q(r_{6−λ,n/2}) ≥ s_{n/2} − (λ−1).
2. So in X(k,l) = Σ_i(i)₄r_{i,k}(l+½)^{−(i+4)} every term has v_q ≥ s_k − (6−i) − (i+4) = s_k − 10, or ≥ s_{n/2} − 9
   when k = n/2.
3. The same bounds hold for c₃ and c₅, with room to spare. The constants (i)₄, 46080 and 860160 are q-units, since
   q ≥ 11 whenever q² > 2.3·40 − 1.
4. This gives v_q(ρ₀), v_q(Z₇), v_q(Z₉) ≥ −E_q^{res}.
5. Finally, s_k ≥ v_q(K_n) = Σ_m⌊N_m/q⌋ − 6⌊n/q⌋. This last expression is an integer > −6, because
   Σ_m⌊N_m/q⌋ > Σ_m N_m/q − 6 = 6n/q − 6. So s_k ≥ −5 and E_q^{res} ≤ 15. ∎

*Proof of (b).*
- Let M := ⌊log_q 2.3n⌋. It bounds every v_q(β): numerator values have |2β| ≤ 2.3n − 1, pole values |β| ≤ n, and the
  δ-value |2β| ≤ n.
- Let ν := v_q(2l+1) ≤ ⌊log_q 2n⌋ ≤ M.
- Lemma D2 gives v_q(r_{6−λ,k}) ≥ s_k − λM, so v_q(X(k,l)) ≥ s_k − max_i[(6−i)M + (i+4)ν] ≥ s_k − 5M − 5⌊log_q 2n⌋.
  The case k = n/2 is similar.
- s_k ≥ v_q(K_n) = Σ_e[Σ_m⌊N_m/q^e⌋ − 6⌊n/q^e⌋]. Each bracket is ≥ −5 by the argument in (c), and it vanishes once
  q^e > max N_m = 1.3n. So s_k ≥ −5⌊log_q 1.3n⌋.
- The bounds for c₃, c₅ are weaker. ∎

*Proof of (a).* This is where the critical zeros enter.
1. **Setup.** Let q > n. Then q is large (q² > n² ≥ 2.3n − 1). No pole value (|j−k| ≤ n) and no nonzero δ-value
   (0 < |n−2k| ≤ n) is divisible by q.
2. **Shape of G_k.** The q-divisible factors of G_k (or H_{n/2}) are therefore exactly the numerator factors
   ε+c−k+½ with q | 2(c−k)+1. Each has e = +1 and v_q = 1, and there are s_k of them.
3. **The r_{i,k}.** By Lemma D2 (second clause), v_q(r_{6−λ,k}) ≥ s_k − min(λ, s_k) ≥ 0. So c₃ and c₅ are q-integral.
4. **X(k,l) with q ∤ 2l+1.** Then X(k,l) is a ℤ_(q)-combination of the r_{i,k}, hence q-integral.
5. **X(k,l) with q | 2l+1.**
   - Put x := l+½ (v_q(x) = 1) and c := k−1−l ∈ [0, n−1]. Then ε−x = ε+c−k+½ is a numerator factor of G_k. By
     Lemma 0(b) it occurs μ(c) ≥ 5 times.
   - So G̃_k := G_k/(ε−x)⁵ is G_k with five q-divisible factors removed. It has v_q(G̃_k(0)) = s_k − 5 and s_k − 5
     remaining q-divisible factors, all with e = +1.
   - By (3.3), X(k,l) = 24[ε⁵]G_k(ε)(x−ε)^{−5} = −24[ε⁵]G̃_k(ε). Lemma D2 gives
     v_q ≥ (s_k−5) − min(5, s_k−5) ≥ 0.
   - For k = n/2 the same argument applied to H gives X = −48[ε⁴]H̃.
6. **Conclusion.** Every X(k,l) is q-integral, hence so is ρ₀. ∎

*Numerical confirmation* (`assembly/resid_check.py` → `resid_check.out`; written from the definitions for this
assembly). The true odd denominators come from the verifier's `truth_E_*.json`: 25 values n = 40, 80, …, 800, 1200,
1600, 2000, 2400, 2800, 3200. At every odd prime:
- the true exponent is ≤ the bound of (b) or (c);
- no prime > n divides the true denominator.

The sharper per-prime procedure of §4.6 was also checked against the truth, at every prime, with no violation:
- for n ≤ 1600 by the verifier (`dproc.py`, `cmp_disc.py`);
- at n = 2000 and 2400 by this assembly, using the verifier's `dproc.py` (`assembly/disc_I_2000.json`,
  `disc_I_2400.json`).

### 4.3 The continuum variables

For large q put x := n/q ≥ 1 and y := k/q ∈ [0, x].

**Lemma D3 (dictionary). PROVED.** For large q, s_k = v(x,y) + [q | n−2k, k ≠ n/2], and s_{n/2} = v(x, x/2), where

  v(x,y) := Σ_{m=1}^{6} #{σ odd : −2(η_m x + y) < σ < 2((1+η_m)x − y)} − 6(⌊y⌋ + ⌊x−y⌋).

*Proof.* For large q every q-divisible factor has v_q exactly 1. Count the factors:
- **Numerator.** 2(c−k)+1 = σq with c ∈ C_m holds iff −2(h_m+k)+1 ≤ σq ≤ 2(n+h_m−k)−1. Since σq is odd and the bounds
  are even ±1, this is the same as −2(h_m+k) < σq < 2(n+h_m−k). Divide by q.
- **Poles.** j − k = τq with j ∈ [0,n] and τ ≠ 0 holds iff −⌊y⌋ ≤ τ ≤ ⌊x−y⌋ and τ ≠ 0.
- **δ-value.** Its valuation is 0 or 1. ∎

Put s(x) := min_y v(x,y) (made precise in Lemma D4) and f⁽⁰⁾(x) := max(0, 10 − s(x)).

**Lemma D4 (structure of s). PROVED.**
(i) **Periodicity.**
- v(x, y+1) = v(x, y): the numerator intervals move by −2, and ⌊y⌋+⌊x−y⌋ is unchanged.
- v(x+40, y) = v(x, y): interval m gains (40+2x_m) odd integers, where x_m = 40η_m, and Σ_m(40+2x_m) = 240 = 6·40.
- Hence s(x+40) = s(x), and the minimum may be taken over y ∈ [0,1).

(ii) **Shape in y.** For fixed x, the function y ↦ v(x,y) on [0,1) is constant on the open intervals cut out by the
14 points 0, {x}, {½−η_m x} and {(1+η_m)x−½}. The pole count ⌊y⌋+⌊x−y⌋ equals ⌊x⌋ on the closed interval [0,{x}] and
⌊x⌋−1 on ({x}, 1).

(iii) **Generic x.** Let C := ⋃_{α∈A}(1/(2α))ℤ, where A := {|γ−γ'| ≠ 0 : γ, γ' ∈ {0, 1, −η_m, 1+η_m}}. For x ∉ C the
14 points are distinct, and s(x) is the minimum of v over the open intervals.
- For every realised (n, q) with x = n/q ∉ C we have min_k s_k ≥ s(x), including k = n/2.
- Reason: a realised y = k/q is never a numerator breakpoint, since 2(h_m+k) is even while σq is odd. The realised
  points y ∈ {0, {x}} take the value of an adjacent open interval, by (ii). The δ-term only increases s_k.

(iv) **Step function.** s is constant on each open interval between consecutive points of C. Two of the 14 points can
coincide mod 1 only if (γ−γ')x ∈ ½ℤ. So on each [1, X], s is a step function with finitely many steps. ∎

### 4.4 Theorem D∞ (residue level) — PROVED (computer-assisted for the value of R⁽⁰⁾)

As n → ∞ with 40 | n,

  log D_n ≤ (10 − R⁽⁰⁾)·n + o(n),   R⁽⁰⁾ := ∫_1^∞ min(10, s(x)) dx/x² = 1.090124192761300787…

*Proof.* Fix X ≥ 1 and split the odd primes q.
- **q > n**: they contribute nothing, by Theorem D(a).
- **q ≤ √(2.3n)**: their total contribution is ≤ 15·π(√(2.3n))·log(3n) = O(√n), by Theorem D(b).
- **Large q with n/q ∈ C ∩ [1, X]**: there are at most #(C ∩ [1, X]) such primes, and each contributes ≤ 15 log n.
- **Large q with n/q ∈ [1, X]∖C**: v_q(D_n) ≤ f⁽⁰⁾(n/q), by Theorem D(c) and Lemma D4(iii). Since f⁽⁰⁾ is a step
  function on [1, X] with steps [a_i, b_i],

    Σ f⁽⁰⁾(n/q)·log q ≤ Σ_i f_i·(θ(n/a_i) − θ(n/b_i)) = n∫_1^X f⁽⁰⁾ dx/x² + o(n),

  by (P5).
- **Large q with n/q > X**: their contribution is ≤ 15·θ(n/X) ≤ 15.3n/X.

Hence limsup (1/n) log D_n ≤ ∫_1^X f⁽⁰⁾dx/x² + 15.3/X. Letting X → ∞ gives the bound ∫_1^∞ f⁽⁰⁾dx/x² = 10 − R⁽⁰⁾. ∎

*The value of R⁽⁰⁾* (PROVED, computer-assisted). By Lemma D4, R⁽⁰⁾ is a finite exact rational sum plus a periodic tail.
- **Head.** ∫_1^{41} min(10,s)dx/x² = Σ_i min(10, s_i)(1/a_i − 1/b_i) over the steps of C ∩ [1, 41]. It equals
  2275273804717574138460377/2189991449667171005856000 = 1.038941866674120584…
- **Tail.** By periodicity and (P9),

    ∫_{41}^∞ min(10,s)dx/x² = (1/40)·Σ_i min(10, s_i)·(ψ(b_i/40) − ψ(a_i/40)) = 0.051182326087180157451…,

  summed over the steps of one period [41, 81].
- **Total.** R⁽⁰⁾ = 1.090124192761300787.

Three independent implementations give identical heads and totals:
- `denominators/cint.py` (prover);
- `verify-denominators/xint.py` (verifier);
- `assembly/rzero.py` (this assembly). It was written from Lemmas D3–D4 alone, and it also checks that s is constant
  at a second point of every step.

Splitting at X = 81 instead of 41 gives a different head and a different tail, but the same total to 22 digits
(`rzero.py`).

The step function begins as follows (f⁽⁰⁾ = 10 − s):

| x | (1, 20/17) | (20/17, 40/29) | (40/29, 20/13) | (20/13, 5/3) | (5/3, 2) | (2, 30/13) | (30/13, 40/17) | … |
|---|---|---|---|---|---|---|---|---|
| s(x) | 0 | −1 | 0 | 1, 2, 3 | 4 | −2 | −1 | … |
| f⁽⁰⁾(x) | 10 | 11 | 10 | 9, 8, 7 | 6 | 12 | 11 | … |

The dx/x²-weight of the values of s over [1, 41] is:

| s | −2 | −1 | 0 | 1 | 2 | 3 | 4 | 5 |
|---|---|---|---|---|---|---|---|---|
| weight | 0.080 | 0.143 | 0.309 | 0.049 | 0.099 | 0.104 | 0.180 | 0.012 |

The losses above 10 (f⁽⁰⁾ = 11, 12) come from the negative shift h₁, and so do the savings.

**Cross-check with L5.** Take ℓ = n−1 with n ∈ I. Then x = n/ℓ ∈ (1, 20/17) and f⁽⁰⁾ = 10, while the second-order bound
of §4.6 gives 9. Theorem A (§7) shows that ℓ⁹ exactly divides D_n. So the one-power saving of Lemma D5 is sharp at
this prime. At n = 2000 the per-prime procedure gives E_ℓ = 9, which equals the true exponent (`disc_I_2000.json`).

### 4.5 What the Theorem needs from L2

Only Theorem D and Theorem D∞ (residue level) are used in §8. They give (10 − R⁽⁰⁾) = 8.9098758 per n, below the
break-even value 9.0990362. This route uses no Andrews-type identity, no second-order lemma and no continuum
bookkeeping beyond Lemma D4.

### 4.6 L2⁺: second- and third-order refinements (not needed for the Theorem) — PROVED (computer-assisted)

These results come from `denominators/proof.md` §§3–8, which contains the full proofs, and were verified in
`verify-denominators/`. They raise R from 1.0901 to 1.4517, which moves the margin from −0.189 to −0.551.

**Lemma D5 (second-order Taylor lemma).** Let q be large, so every v_q(β) ≤ 1. Put P(u) := ∏_{v_q(β)=1}(1+u/β')^{e_β},
with β' := β/q a q-unit, and p_j := [u^j]P. Then

  [ε^λ]Π = Σ_{j≤λ} q^{−j}p_j u_{λ−j}   (u_i ∈ ℤ_(q), u₀ = 1),

so v_q([ε^λ]Π) ≥ −max_{j≤λ}(j − v_q(p_j)). Also [ε^λ]Π ≡ q^{−λ}p_λ (mod q^{1−λ}) when v_q(p_λ) = 0.

*Proof.* Π(ε) = P(ε/q)·U(ε), and both factors have q-integral coefficients. ∎

The key identity is [u^{r−1}](1−u)^{−r}(1−2u) = C(2r−2,r−1) − 2C(2r−3,r−1) = 0. For P = (1−u)^{−6}(1−2u), for example,
p₅ = 0 and p₄ = +14. So a Taylor coefficient that Lemma D2 puts at q^{−5} is really O(q^{−4}). On
x ∈ (1, 20/17) ∪ (10/7, 20/13) this gains exactly one power, which adds exactly 1/5 to R:
**R⁽²⁾ = R⁽⁰⁾ + 1/5 = 1.290124192761300787**.

**Lemma D6 (absorbed form; uses the critical zeros).** For 0 ≤ c ≤ n−1, l = k−1−c and x = l+½:

  X(k,l) = −24·G_k(0)·(−x)^{−5}·[ε⁵]Π'_{k,c}(ε),

where Π'_{k,c} is Π_k with five copies of (1−ε/x) removed. (This is the computation in the proof of Theorem D(a).)

**Lemma D7 (anti-diagonal root identity).** Σ_{k=0}^{n} X(k, k−1−c) = 0 for every c ∈ [0, n−1].

*Proof.* By Lemma 0(b), R_n vanishes to order ≥ 5 at t_c = −½−c, so R_n^{(4)}(t_c) = Σ_k PP_k^{(4)}(t_c) = 0. Also
t_c + k = (k−1−c) + ½. (This is Lai's root trick [Lai, Lemma 4.6], written per anti-diagonal.) ∎

*Consequence (switch).* ρ₀ = Σ_c Σ_{k>c} X(k,k−1−c) = −Σ_c Σ_{k≤c} X(k,k−1−c). So for each anti-diagonal the better of
the two one-sided bounds may be used.

**Lemma D8 (Wilson translation).** Let q be large, let k, k+q ∈ [0,n] and q ∤ n−2k. Write Û_k := G_k(0)/q^{s_k}, a
q-unit. Let D_q(k) be the local data, i.e. the q-divisible pole partners, numerator indices and δ-index. Let
Q(D_q(k)) := ∏ j^{−6}·∏(σ/2)·(t/2) be the product of their normalised values. Then s_{k+q} = s_k and

  Û_{k+q}/Q(D_q(k+q)) ≡ Û_k/Q(D_q(k)) (mod q).

*Proof.* Compare (3.1) at k and at k+q:
- The δ-ratio is ≡ 1.
- Numerator blocks shift by −q. Unit factors contribute ≡ 1, and a q-divisible factor σq/2 becomes (σ−2)q/2.
- The pole ratio is a quotient of two products of q consecutive integers. By Wilson, each has unit part ≡ −1, and
  their q-multiples are exactly the partner values. ∎

**Lemma D9 (reflection).** Û_{n−k} = −Û_k and Q(D_q(n−k)) = (−1)^{N(k)}·Q(D_q(k)), where N(k) is the number of
q-divisible numerator factors.

*Proof.* Use G_{n−k}(ε) = −G_k(−ε) (Lemma 0(c)). ∎

**Proposition D10 (row cancellation).** Let q be large and let l be a *bad row* (q | 2l+1 = σq). Put
T_l := Σ_{k>l} X(k,l). Let β* be the minimum over k > l of the Lemma D5/D6 bounds, and let K* be the set of k where
the minimum is attained. Assume:
- (i) for every k ∈ K*: q ∤ n−2k, k ≠ n/2, and p₅(P_k(1−2u/σ)^{−5}) is a q-unit;
- (ii) for every residue class κ mod q: Ψ(κ) = (−1)^{N(κ)}·Ψ(n−κ), where
  Ψ(κ) := Σ_{k∈K*, k≡κ} Q(D_q(k))·p₅(P_k(1−2u/σ)^{−5}).

Then v_q(T_l) ≥ β* + 1.

*Proof.*
1. For k ∈ K*, X(k,l) ≡ 768σ^{−5}q^{β*}·Û_k·p₅ (mod q^{β*+1}).
2. By Lemma D8, Û_k ≡ W(κ)Q(D_q(k)) with W(κ) depending only on κ = k mod q.
3. By Lemma D9, W(n−κ) = −(−1)^{N(κ)}W(κ).
4. Pair κ with n−κ; (i) ensures no class is paired with itself. By (ii), each pair contributes 0 mod q^{β*+1}. ∎

**Theorem D∞⁺ (sharper asymptotics).** Define f(x) on [1, 41] as the continuum version of the per-prime procedure:
the switch bound with the Lemma D5 losses, and Prop. D10 whenever its (continuum) hypotheses hold. f is constant on
the intervals between the 1217 points of C ∩ [1, 41] (the argument of Lemma D4(iv)), and discrete ≤ continuum
(`denominators` Lemma 8.1). The PNT argument of §4.4 then gives

  log D_n ≤ (10 − R_E)n + o(n),   R_E := ∫_1^{41}(10 − f)dx/x² + ∫_{41}^∞ min(10, s)dx/x² = 1.451704999621994665…

The head is the exact rational 9876623266560421249/7052098086803952000; the tail is 0.051182326087180157451. Both
were reproduced exactly by the verifier's independent `xcont.py`/`xint.py`.
- With X₁ = 11 instead of 41, R = 1.4322937593 (head 1367647/1108800).
- On the uniform (6,3) family the same f equals 9 = a+j on all of [1, 12]. This recovers the one-power
  Andrews-transformation saving of LSZ Lemma 5.3 without Andrews.

*Numerical confirmation of L2⁺* (verifier):
- the continuum f against the true exponents: 2081 large primes, n = 200–3200, 0 violations; f is exact except at
  1–7 primes per n;
- the discrete procedure equals the continuum bound at all 609 large primes checked (n = 400–1600);
- Lemma D7 holds exactly for all c; Lemma D8 holds on about 14 000 pairs (k, k+q); Prop. D10 was checked on every row
  where its criterion applies;
- the fully proved per-n bound at n = 2000 is ln D/n ≤ 8.5730, against the true value 8.5437.

---------------------------------------------------------------------------------------------------

## 5. L3 — 2-adic smallness (GAP 4) — PROVED + NUMERICAL

**Theorem G4** (`valuation/proof.md`; verified in `verify-valuation/`). Let n ≥ 0, a ≥ 1, j ≥ 0 and δ ∈ {0,1}. Let
h ∈ ℤ^a satisfy Σh_m = 0 and N_m := n + 2h_m ≥ 0, with no sign condition on the h_m. Put

  R(t) = (2t+n)^δ∏_m(t+½−h_m)_{N_m}/(t)_{n+1}^a,   S = ∫_{ℤ₂}R^{(j)}(t+½)dt,

σ := Σ_m s₂(N_m), N* := max(1, N_m) and λ := ⌊log₂N*⌋ + 1. Then

  v₂(S) ≥ 2an + a + j − σ − (j+1)λ.

**For configuration E** ((a,j,δ) = (6,3,1) and N* = 1.3n):

  v₂(S_n) ≥ 12n + 9 − σ_n − 4λ_n ≥ 12n + 9 − 10λ_n ≥ 12n − 1 − 10·log₂(1.3n).        (5.1)

The middle step uses σ ≤ 6λ.

**The Δ-calculus.** For f: ℤ₂ → ℚ₂ put

  Δ₀(f) := inf_{k≥1} v₂((f(k)−f(k₋))/(k−k₋)),   Δ(f) := min{1+v₂(f(0)), Δ₀(f)}.

Clearly Δ(f+g) ≥ min(Δf, Δg) and Δ(Cf) = Δf + v₂(C).

(D1) *If f ∈ S¹(ℤ₂,ℚ₂), then v₂(∫f) ≥ Δ(f) − 1.*
*Proof.* 2^{−M}Σ_{k<2^M}f(k) = f(0) + Σ_{l<M}Σ_{k=2^l}^{2^{l+1}−1}(f(k)−f(k₋))/2^{l+1}. This holds because
consecutive Riemann sums differ by 2^{−(l+1)}Σ_{2^l≤k<2^{l+1}}(f(k)−f(k−2^l)), and k−2^l = k₋ on that range. Each
summand is ½·(f(k)−f(k₋))/(k−k₋). So every Riemann sum lies in the closed set 2^{Δ−1}ℤ₂, and so does the limit. ∎

(D2) *If f, g ∈ S¹(ℤ₂,ℤ₂), then Δ(fg) ≥ min(Δf, Δg).*
*Proof.* (fg(k)−fg(k₋))/(k−k₋) = g(k₋)·(f(k)−f(k₋))/(k−k₋) + f(k)·(g(k)−g(k₋))/(k−k₋). ∎

(D3) *If f = Σe_it^i with e_i ∈ ℤ₂ and e_i → 0, then f ∈ S¹(ℤ₂,ℤ₂) and Δ(f) ≥ 0.*
*Proof.* The divided differences are Σ_i e_iΣ_{u<i}x^u y^{i−1−u}, which lie in ℤ₂. ∎

(D4) *If x ∈ ℤ (any sign), L ≥ 1 and f = C(t+x, L), then Δ(f) ≥ −⌊log₂L⌋.*
*Proof.* Vandermonde's identity holds over ℤ, so C(k+x,L) = Σ_iC(k−k₋,i)C(k₋+x,L−i). Hence

  (f(k)−f(k₋))/(k−k₋) = Σ_{i=1}^{L}(1/i)·C(k−k₋−1, i−1)·C(k₋+x, L−i),

which has valuation ≥ −⌊log₂L⌋. Also f(0) ∈ ℤ. ∎

**Lemma V1 (factorisation).**

  R(t+½) = 2^{a(n+1)}·E(t)·∏_m N_m!·C(t+n+h_m, N_m),   E(t) := (2t+1+n)^δ∏_{k=0}^{n}(2t+2k+1)^{−a}.

*Proof.*
- (t+1−h)_N = ∏_{l=1−h}^{n+h}(t+l) = N!·C(t+n+h, N) for either sign of h. (When h ≥ 1 the block contains the harmless
  zeros t = 0, …, h−1.)
- (t+½)_{n+1} = 2^{−n−1}∏_k(2t+2k+1). ∎

**Lemma V2.** E_β := E^{(β)}/(β!2^β) lies in S¹(ℤ₂,ℤ₂) and satisfies Δ(E_β) ≥ 0.
*Proof.* E is a product of the factors (2t+c)^{−1} (c odd) and possibly 2t+1+n. Each derivative of (2t+c)^{−1} brings
a factor 2. Each (2t+c)^{−e} = c^{−e}Σ_r C(−e,r)2^r c^{−r}t^r satisfies (D3). Conclude with (D2). ∎

**Lemma V3 (derivatives of binomials).** (d/dt)^μ C(t+x,N) = Σ_{r=μ}^{N} c_{μ,r}·C(t+x, N−r), where
c_{μ,r} = [z^r](log(1+z))^μ. Moreover v₂(c_{μ,r}) ≥ −μ⌊log₂r⌋.
*Proof.*
- Σ_N C(t+x,N)z^N = exp((t+x)log(1+z)): both sides are polynomial in t coefficientwise and agree for t+x ∈ ℤ_{≥0}.
- Differentiate μ times in t.
- Each term of c_{μ,r} is ∏_k(±1/i_k) with 1 ≤ i_k ≤ r. ∎

**Lemma V4 (term decomposition).** By Leibniz,

  R^{(j)}(t+½) = Σ K(β,μ,r)·Φ_{β,r}(t),

where
- K = 2^{a(n+1)}(j!/∏μ_m!)2^β∏_mN_m!∏_mc_{μ_m,r_m};
- Φ_{β,r} = E_β∏_mC(t+n+h_m, N_m−r_m);
- the sum runs over β + Σμ_m = j and μ_m ≤ r_m ≤ N_m (with r_m = 0 when μ_m = 0).

The valuations satisfy

  v₂(K) ≥ a(n+1) + β + (an − σ) − Σ_mμ_m⌊log₂N_m⌋ ≥ 2an + a + β − σ − (j−β)(λ−1).

Here v₂(∏N_m!) = Σ(N_m − s₂(N_m)) = an + 2Σh_m − σ = an − σ. This is the only place where Σh = 0 is used.

**Lemma V5.** Φ_{β,r} ∈ S¹(ℤ₂,ℤ₂) and Δ(Φ) ≥ −(λ−1), hence v₂(∫Φ) ≥ −λ. This follows from (D2) and (D4); negative
offsets n+h_m are allowed.

*Proof of G4.* The sum is finite and each term lies in S¹, so S = ΣK·∫Φ, and

  v₂(K∫Φ) ≥ 2an + a + β − σ − (j−β)(λ−1) − λ = 2an + a + j − σ − (j+1)λ + βλ. ∎

*Numerical confirmation.*
- **Config E table** (true v₂(S_n) / refined bound (5.1)):
  - n = 40: 457 / 447; n = 200: 2365 / 2347; n = 400: 4763 / 4743; n = 640: 7649 / 7631;
  - the verifier added n = 520 (6199 / 6184) and n = 600 (7159 / 7139).
  - So 12n − v₂(S_n) ranges over 23..41 for 40 ≤ n ≤ 640.
- **Sweeps.** 2839 prover cases and 3265 verifier cases, including extreme h, n ≤ 511 and n = 2^m−1: 0 violations. The
  bound is attained in some small cases.
- **Evaluators.** Two independent direct evaluators of S from the Volkenborn definition (Mahler series; Bernoulli
  numbers) agree with the partial-fraction ledgers.
- **Remark.** The 2-power part of any common denominator cancels in the criterion (§8). GAP 4 is therefore needed only
  in the form (5.1).

---------------------------------------------------------------------------------------------------

## 6. L4 — archimedean growth of ρ₀, Z₇, Z₉ (GAP 1)

**Theorem G** (`growth/proof.md`; verified in `verify-growth/`). **PROVED (computer-assisted).**
- For every n ≡ 0 (mod 40) with n ≥ 2000,

    max(|ρ₀|, |Z₇|, |Z₉|) ≤ 1.56·10¹²·n^{−4}·e^{−0.7812n}.

- **Theorem G′.** For n ≡ 0 (mod 40) with n ≥ 10⁴, the same holds with 3.31·10¹¹·n^{−4}·e^{−0.78127n}.
- In particular limsup (1/n)·log max(|ρ₀|,|Z₇|,|Z₉|) ≤ −0.78127 =: g.

*Why this is not routine.* The top residues have size |r_{6,k}| ≈ e^{nP(−k/n)}, where P is the real profile of §6.4,
and max P = P(−0.3485) = +0.8210. So each coefficient hides about 1.60 nats per n of cancellation between different
poles k. Any bound of the form Σ_k|…| (Cauchy, residues) gives a positive rate and destroys the margin.

### 6.1 Kernels (Lemma K) — PROVED

Put q := e^{2πit} and

  K₂ := (π sec πt)² = 4π²q/(1+q)²,   K₄ := (π sec πt)⁴ = 16π⁴q²/(1+q)⁴,   W := (d/dt)⁴(π tan πt) = 8π⁵T(1+T²)(2+3T²),

where T = tan πt. These kernels have the following properties.
- (a) **Periodicity.** They have period 1 and are holomorphic off ℤ+½, in particular at every integer.
- (b) **Taylor data at the integers.**
  K₂(−k+u) = π² + π⁴u² + (2/3)π⁶u⁴ + O(u⁶) and K₄(−k+u) = π⁴ + 2π⁶u² + (7/3)π⁸u⁴ + O(u⁶).
- (c) **Poles at half-integers.** K₂ and K₄ have poles of order 2 and 4. W(x+u) = −24u^{−5} + (holomorphic).
- (d) **Decay.** For |Im t| ≥ 1: |K₂| ≤ 39.626e^{−2π|Im t|}, |K₄| ≤ 2.9323e^{−2π|Im t|} and |W| ≤ 10088.01e^{−2π|Im t|}.
  These follow from the q-expansions, e.g. W = 2πi(2π)⁴Σ_{k≥1}(−1)^k k⁴q^k.
- (e) **Bounds on Re t ∈ ℤ.** There |K₂| ≤ π², |K₄| ≤ π⁴ and |W| ≤ 16π⁵.
- (f) **Symmetry.** K(t̄) = conj K(t). K₂ and K₄ satisfy K(−n−t) = K(t), while W(−n−t) = −W(t) (n even).

### 6.2 Proposition 3 (exact contour representations) — PROVED + NUMERICAL

Let c := n/40 ∈ ℤ. Let Γ be an upward contour from −i∞ to +i∞ with these properties:
- for large |Im t| it lies in a fixed vertical strip;
- it crosses ℝ exactly once, at c;
- it is symmetric under conjugation.

Examples are the line Re t = c and the contour Γ_n of §6.5. Then

 (a) V₂ := π⁴c₃ + (2/3)π⁶c₅ = (1/πi)∫_Γ R_nK₂ dt,
 (b) V₄ := 2π⁶c₃ + (7/3)π⁸c₅ = (1/πi)∫_Γ R_nK₄ dt,
 (c) I := Σ_{ν≥0}R_n^{(4)}(ν+½) = 45720ζ(7)c₃ + 858480ζ(9)c₅ − ρ₀ = (1/2πi)∫_Γ R_nW dt,

where 45720 = (3)₄(2⁷−1) and 858480 = (5)₄(2⁹−1). Solving back:

  c₅ = (V₄ − 2π²V₂)/π⁸,   c₃ = ((7/3)V₂ − (2/3)π^{−2}V₄)/π⁴,   ρ₀ = 45720ζ(7)c₃ + 858480ζ(9)c₅ − I.        (6.1)

*Proof.*
1. **Contour independence.** R_nK is holomorphic in the open half-planes and is O(|t|^{−5}e^{−2π|Im t|}) there, by
   Lemma 0(a) and Lemma K(d). So by Cauchy all admissible contours give the same integral. Take Γ = {Re t = c}.
2. **(a), (b).** In the strip −n−c < Re t < c the half-integers are removable singularities of R_nK. Indeed
   ord R_n ≥ 5 there (Lemma 0(b)), while the pole order of K is ≤ 4.
   - At −k: Res R_nK₂ = π²r_{1,k} + π⁴r_{3,k} + (2/3)π⁶r_{5,k}, and similarly for K₄.
   - Sum over k and use c₁ = 0 (Lemma 0(d)). By the residue theorem the result is (1/2πi)(∫_{Re t=c} − ∫_{Re t=−n−c}).
   - The substitution t = −n−s turns the second integral into −∫_{Re s=c}, because R_nK is odd under t ↦ −n−t
     (Lemma 0(c), Lemma K(f)).
3. **(c).** To the right of c, R_nW has poles only at the half-integers x > c, with residue −24[u⁴]R_n(x+u) = −R_n^{(4)}(x).
   - At the half-integers 0 < x < c we have R_n^{(4)}(x) = 0, since ord ≥ 5 there (Lemma 0(b)). **This is the critical-zero
     condition.**
   - Close the contour at Re t = N → ∞: there |R_n| = O(N^{−5}) and |W| ≤ 16π⁵ (Lemma K(e)).
   - This gives (1/2πi)∫_{Re t=c}R_nW = Σ_{ν≥0}R_n^{(4)}(ν+½).
   - Finally R_n^{(4)} = Σ(i)₄r_{i,k}(t+k)^{−i−4}, and Σ_{ν≥0}(ν+k+½)^{−s} = (2^s−1)ζ(s) − A_k^{(s)}. ∎

*Numerical confirmation.*
- The three identities hold to relative error 10^{−40} (prover, n = 40, 80). The verifier confirmed them on three
  different contours.
- A negative control that crosses at c+1 breaks only (c), as predicted.
- Along the proof contour Γ_n (§6.5), the right-hand sides reproduce ln|ρ₀|/n, ln|Z₇|/n and ln|Z₉|/n to 6 digits at
  all 12 exact n = 120, …, 640.

### 6.3 Pointwise bounds for |R_n| — PROVED + NUMERICAL

Put F(z) := z log z − z and g(z) := z log z (principal branch, continuous on the closed upper half-plane with g(0) = 0),
and

  L(t) := log|2t+n| + Σ_mRe[F(t+n+h_m) − F(t−h_m)] − 6Re[F(t+n+½) − F(t−½)],
  φ(τ) := Σ_m[g(τ+1+η_m) − g(τ−η_m)] − 6[g(τ+1) − g(τ)].

- **Lemma 4 (midpoint rule).** For Im t ≥ 1, |log|R_n(t)| − L(t)| ≤ (π+3)/2.
  *Proof.* Compare each linear-factor block with the integral of log|t+b+s|; the endpoints are t+n+h_m, t−h_m and
  t+n+½, t−½. The cell error is ≤ max|f''|/24, and Σ_cells max|f''| ≤ π/y + 3/y² ≤ π+3. There are 12 blocks. ∎
- **Lemma 5 (scaling).** For Im τ > 0, Re τ ≥ 0 and |τ| > δ := 1/(2n):

    L(nτ) ≤ n·Re φ(τ) − 5 log n + log|2τ+1| − 3 log(|τ|−δ).

  *Proof.* Use F(nz) = ng(z) + n(log n − 1)z and Ση = 0. The δ-shifts are controlled by Re g' = log|·| + 1. ∎
- **Lemma 6 (crossing segment).** For c ∈ ℤ_{≥1} and |y| ≤ 1, |R_n(c+iy)| ≤ e^{π²/2}|R_n(c+i)|.

Together they give, for Im(nτ) ≥ 1 and Re τ ≥ 0,

  log|R_n(nτ)| ≤ n·Re φ(τ) + E_n(τ),   E_n(τ) := −5 log n + log|2τ+1| − 3 log(|τ|−1/(2n)) + (π+3)/2.        (6.2)

On the contour below |τ| ≥ 1/40, so E_n ≤ 14.218 − 5 log n for n ≥ 2000.

### 6.4 The landscape Ψ := Re φ − 2π Im τ

On the real axis P(x) := Re φ(x+i0) is the real profile, and P(−1−x) = P(x).

*Saddle point (NUMERICAL, explanatory only).* The critical points solve φ'(τ) = −2πi. The relevant one is
τ* = 0.0695900497 + 0.0312802763i, with Ψ(τ*) = −0.7812761397. On the real axis near the crossing point,
P(0.025) = −0.8005 < Ψ(τ*), so the saddle, not the crossing, sets the rate.

**Lemma 7 (PROVED, computer-assisted).**
 (i) P(x) ≤ 0.85 on [−0.5, 0.15] (sharp version: ≤ 0.8215; the true maximum is 0.820998 at x = −0.34848).
 (ii) Ψ ≤ −0.7812 on [0.025, 0.070] × [0, 0.001] (sharp: ≤ −0.78127 on [0.025, 0.0697] × [0, 10^{−4}]).
 (iii) Ψ ≤ −0.7812 on [0.069, 0.070] × [0, 0.26] (sharp: ≤ −0.78127 on [0.0695, 0.0697] × [0, 0.26]).

*Certification.* Three rigorous certifications with three different bounding methods:
- **Prover** (`growth/certify.py`, `certify_sharp.py`): mpmath.iv interval arithmetic, 96-bit, outward rounding. It uses
  the plain enclosure and the centred form, arg enclosed at the corners, a special enclosure for boxes containing a
  branch point, and bisection.
- **Verifier** (`verify-growth/vcertify.py`): exact rational boxes. It uses a harmonic second-order Taylor bound
  (|φ''| ≤ Σ|s_j|/d_j) and a monotone-corner bound near the branch points. Point values of log and atan2 again come
  from mpmath.iv, at 120 bits.
- All six inequalities are certified by both methods. Controls with targets just below the true maxima fail, and
  targets just above pass, so the test is sensitive.
- 12 000 random point tests and 2427 random box tests gave 0 violations.
- The prover's box endpoints are 53-bit floats, so x = 1/40 and x = 0.15 lie outside its boxes by about 10^{−18}.
  They are covered by the exact-rational boxes of the verifier's run and of the third certification.
- **Third certification, independent of mpmath** (this assembly, `assembly/cert3.py` and `cert3b.py`).
  - *Arithmetic.* Exact rationals, and integer intervals at scale 2^{−128} with explicit floor/ceil rounding.
  - *Elementary functions*, all with explicit remainder bounds:
    - log r = k log 2 + 2 atanh((m−1)/(m+1));
    - atan by alternating series, with π from Machin's formula;
    - 1/e by its series.
  - *Box bound.* The minimum of two bounds:
    - exact per-term extrema of Re g over each translated box, using only ∂_y Re g = −arg z ≤ 0 and the sign of
      ∂_x Re g = log|z| + 1. On the circle |z| = 1/e, the interior local maximum is ≤ 1/e − yπ/2 and the interior
      local minimum is ≥ −1/e − yπ/2.
    - near the saddle, a centred mean-value bound Ψ(m) + sup|∂_xΨ|·h_x + sup|∂_yΨ|·h_y, where ∂_xΨ = Σs_j log|z_j| and
      ∂_yΨ = −Σs_j arg z_j − 2π are enclosed over the box. This is used only on boxes whose translates avoid the
      branch point 0.
  - *Results, all CERTIFIED:*

    | version | (i) | (ii) | (iii) |
    |---|---|---|---|
    | standard | P ≤ 0.85 (33 boxes) | Ψ ≤ −0.7812 (23 boxes) | Ψ ≤ −0.7812 (283 boxes) |
    | sharp | P ≤ 0.8215 (53 boxes) | Ψ ≤ −0.78127 (19 boxes) | Ψ ≤ −0.78127 (157 boxes) |

    Weaker sets are also certified: P ≤ 0.9 with Ψ ≤ −0.75, and P ≤ 0.85 with Ψ ≤ −0.78, the latter by the per-term
    bound alone.
  - *Negative controls* with targets just below the true maxima all fail, at the correct locations:
    - 0.8209 on (i);
    - −0.7930 on (ii);
    - −0.7813 and −0.78126 on (iii), whose true maximum is −0.7812591 at x = 0.069.
  - *Consequence.* Lemma 7, and hence Theorems G and G′, no longer depend on mpmath. What remains is the correctness
    of about 440 lines of new code.

**Lemma 8 (PROVED).** Re φ ≤ 0.85 (sharp: 0.8215) on the closed upper half-plane. Hence Ψ ≤ −0.7836 for
Im τ ≥ 0.26 (sharp: ≤ −0.8121).

*Proof.*
1. **Right tail, x ≥ 0.15.** The map η ↦ g(x+1+η) − g(x−η) is concave on [−½, x], which contains every η_m and their
   mean 0. By Jensen, P(x) ≤ 0.
2. **Left tail, x ≤ −1.15.** Re φ(−1−τ̄) = Re φ(τ), so P ≤ 0 there too, and sup_ℝP = max_{[−0.5,0.15]}P ≤ 0.85 by
   Lemma 7(i).
3. **Upper half-plane.** Re φ is harmonic in H, continuous on H̄, and O(τ^{−2}) at ∞, since the "masses" of φ satisfy
   Σs = Σsa = Σsa² = 0. Apply the maximum principle on large half-discs. ∎

(The prover's text stated concavity on (−x−1, x). The verifier corrected this to [−½, x]; the conclusion is
unaffected.)

### 6.5 Assembly — proof of Theorems G and G′

Fix n ≡ 0 (mod 40) with n ≥ 2000, and let x₁ := ⌊0.0696n⌋, so x₁/n ∈ [0.0691, 0.0696]. Let Γ_n⁺ be the path

  A: c → c+i,   B: c+i → x₁+i,   C: x₁+i → x₁+i∞,

and let Γ_n := conj(Γ_n⁺) ∪ Γ_n⁺. It is admissible for Proposition 3, and ∫_Γ = 2i·Im∫_{Γ⁺}. Estimate the pieces:
- **Piece A.** Use Lemma 6, Lemma K(e), and (6.2) at τ = 1/40 + i/n together with Lemma 7(ii).
- **Piece B.** Use (6.2) with Lemma 7(ii) at height 1/n ≤ 0.001, over a length ≤ 0.0446n.
- **Piece C.** Use Lemma 7(iii) up to height 0.26n, and Lemma 8 beyond, whose contribution is
  ∫e^{0.85n−2πy}dy ≤ e^{−0.7836n}/(2π).

Altogether

  J_K := ∫_{Γ⁺}|R_nK||dt| ≤ n^{−5}e^{14.218}e^{−0.7812n}[κ_K^A e^{π²/2+2π} + κ_K(0.3046n + 1/(2π))].

Inserting this into (6.1), with ζ(7) ≤ 1.0084 and ζ(9) ≤ 1.0021, gives the constants of n^{−4}e^{−0.7812n}:

| |V₂| | |V₄| | |I| | |Z₇| | |Z₉| | |ρ₀| |
|---|---|---|---|---|---|
| 3.61·10⁸ | 3.45·10⁹ | 8.82·10¹⁰ | 5.09·10¹¹ | 9.59·10¹¹ | 1.56·10¹² |

The verifier's interval recomputation gives C_G = 1.5548·10¹² ≤ 1.56·10¹². Theorem G′ is the same argument with the
sharp versions and n ≥ 10⁴; its constant is 3.3070·10¹¹ ≤ 3.31·10¹¹. ∎

### 6.6 Sharpness and robustness (NUMERICAL)

The contour representation reproduces the exact coefficients at n ≤ 640. It gives (1/n)·log max|coef| = −0.7954,
−0.7900, −0.7864, −0.7829 and −0.7818 at n = 10³, 2·10³, 4·10³, 1.6·10⁴ and 6.4·10⁴, converging to Ψ(τ*). The
effective prefactor is about n^{−4.5}.

**Robustness.** The Theorem needs only g < −0.5921 on the minimal route of §8 (and g < −0.2305 with R_E). The
certified value −0.7812 has slack ≥ 0.19.
- Even the weakest certified set (P ≤ 0.9, Ψ ≤ −0.75), which needs neither the centred form nor mpmath, gives
  g = −0.75.
- With it the margins would be −0.158 with R⁽⁰⁾ and −0.519 with R_E.

---------------------------------------------------------------------------------------------------

## 7. L5 — ℓ-adic separation at ℓ = n − 1 (GAP 3) — PROVED + NUMERICAL

This section follows `nonvanishing/proof.md`, verified in `verify-nonvanishing/`, rewritten in the conventions of
§3: X(k,l) uses l + ½ with 0 ≤ l < k.

**Theorem A.** Let 40 | n, let ℓ := n − 1 be prime, and let ℓ ≠ 91079 (equivalently n ∈ I; the smallest such n is
80). Then

  v_ℓ(ρ₀) = −9,   ℓ⁹ρ₀ ≡ 168·Γ₀·K (mod ℓ),   v_ℓ(Z₇) ≥ −3,   v_ℓ(Z₉) ≥ −1,

where:
- K := 80T − 8 = 12386744/345345 = 2³·17·91079/(3·5·7·11·13·23), with T := Σ_m 1/(x_m+20) and
  x = (−17, 1, 2, 3, 5, 6);
- Γ₀ := n·∏_m∏_{c∈C_m, c≠n/2−1}(c+½) / ∏_{1≤j≤n, j≠n−1} j⁶ is an ℓ-adic unit.

**Size facts** (valid for n ≥ 80). All the integers below lie in (−3ℓ, 3ℓ).
- (S1) Pole values j−k (j ≠ k) have |j−k| ≤ n = ℓ+1. So ℓ | j−k only when {j,k} = {0, ℓ} or {1, n}.
- (S2) Numerator values 2(c−k)+1 (c ∈ C_m) are odd with |·| ≤ 2.3n−1 < 3ℓ. So ℓ divides one only when it equals ±ℓ,
  i.e. c = k+n/2−1 or c = k−n/2. These values lie in C_m exactly when k ≤ n/2+h_m, respectively k ≥ n/2−h_m. (The other
  endpoint conditions hold automatically, since −17n/40 > 1−n/2.)
- (S3) n−2k is even with |n−2k| ≤ n < 2ℓ, so it is an ℓ-unit unless k = n/2.
- (S4) 2l+1 ∈ [1, 2n−1] = [1, 2ℓ+1]. So ℓ | 2l+1 only for l = l* := n/2 − 1.
- (S5) (i)₄, 46080 and 860160 are ℓ-units.

**Lemma A1 (local shape at ℓ).** Let e_k(m) := [k ≤ n/2+h_m] + [k ≥ n/2−h_m] and e_k := Σ_m e_k(m).
- (a) **Middle poles, 2 ≤ k ≤ n−2.** Here e_k ≥ 5, because every m with h_m ≥ 0 satisfies one of the two conditions,
  and there is no ℓ-divisible pole value (S1). Write G_k = ∏_{s≤e_k}(ε+α_s)·Γ_k with α_s = ±ℓ/2 and Γ_k ∈ ℤ_(ℓ)[[ε]].
  Then v_ℓ([ε^μ]G_k) ≥ e_k − μ, i.e. **v_ℓ(r_{i,k}) ≥ i − 1**. For k = n/2 the same holds, with the factor 2ε.
- (b) **Singular poles k ∈ {0,1}.** Here e_k(m) = 1 for every m, since n/2+h₁ = 3n/40 ≥ 6 and n/2−h₆ = 7n/20 > 1. So

    G_k(ε) = Q(ε)·Γ_k(ε),   Q(ε) := ((ε+ℓ/2)/(ε+ℓ))⁶ = 2^{−6}((1+2ε/ℓ)/(1+ε/ℓ))⁶,

  with Γ_k ∈ ℤ_(ℓ)[[ε]] and Γ_k(0) ∈ ℤ_(ℓ)^×. The unit property holds because n−2k ∈ {n, n−2} ≡ ±1 and all remaining
  values are ℓ-units.
- For k ∈ {n−1, n}, symmetrically, G_k = Q(−ε)Γ_k.
- Since [ε^μ]Q(±ε) = (±1)^μ2^{−6}a_μℓ^{−μ} with a_μ := [x^μ]((1+2x)/(1+x))⁶ = 1, 6, 9, −4, −6, 12, −10 (μ = 0..6):
  **v_ℓ(r_{i,k}) ≥ i − 6** at the four singular poles.
- (c) Consequently v_ℓ(c_i) ≥ i − 6, so **v_ℓ(Z₇) ≥ −3 and v_ℓ(Z₉) ≥ −1** by (S5). ∎

**Lemma A2 (reduction to two terms).** Put Λ[G] := Σ_{i=1}^{6}(i)₄·[ε^{6−i}]G·(−ℓ/2)^{−(i+4)}. Then

  ρ₀ ≡ X(n−1, l*) + X(n, l*) = −(Λ[G₀] + Λ[G₁])   (mod ℓ^{−5}ℤ_(ℓ)).

*Proof.* Classify the terms of ρ₀ = Σ_{0≤l<k≤n}X(k,l):
- For l ≠ l*, l+½ is an ℓ-unit (S4), so v_ℓ(X(k,l)) ≥ min_i v_ℓ(r_{i,k}) ≥ −5 by Lemma A1.
- For l = l* and n/2 ≤ k ≤ n−2, v_ℓ(X(k,l*)) ≥ min_i(i−1−(i+4)) = −5.
- The two remaining terms satisfy the exact identities X(n, l*) = −Λ[G₀] and X(n−1, l*) = −Λ[G₁]:
  - apply (3.2) to X(k,l) = PP_k^{(4)}(l+½−k), which gives X(n, l*) = −PP₀^{(4)}(−ℓ/2);
  - and X(n−1, l*) = −PP₁^{(4)}(−(n+1)/2), where (−(n+1)/2) + 1 = −ℓ/2. ∎

*Remark.* The prover derived the same congruence from Lai's root trick. The two central half-integers −½−(n/2−1) and
−½−n/2 are zeros of order exactly 6 (Lemma 0(b)), so R_n^{(4)} vanishes there. Both routes were checked exactly.

**Lemma A3 (universal local factor).** For k ∈ {0,1} let γ_{k,λ} := [ε^λ]Γ_k. Then

  Λ[G_k] = Σ_{λ=0}^{5} β_λ ℓ^{λ−10} γ_{k,λ},   β_λ := 2^{−6}Σ_{i=1}^{6−λ}(i)₄(−2)^{i+4}a_{6−i−λ},

and (β₀, …, β₅) = (0, −168, 168, −108, 48, −12). Hence Λ[G₀] + Λ[G₁] ≡ −168ℓ^{−9}(γ_{0,1}+γ_{1,1}) (mod ℓ^{−8}).

*Proof.*
- The formula follows from Λ[ε^λQ] = ℓ^{λ−10}β_λ.
- Why β₀ = 0: F(ε) := Q(ε)ε^{−6} is the sum of its principal parts at 0 and at −ℓ. Since F(−ℓ−ε) = F(ε), we have
  P_{−ℓ}(ε) = P₀(−ℓ−ε). F has a zero of order 6 at −ℓ/2, so 0 = F^{(4)}(−ℓ/2) = 2P₀^{(4)}(−ℓ/2) = 2Λ[Q]. This uses that
  j+1 = 4 is even.
- The values of β were recomputed in `assembly/constants.out`. ∎

**Lemma A4 (the two singular poles).**
- **Ratio.** Γ₁(0)/Γ₀(0) = r_{6,1}/r_{6,0} = ((n−2)/n)·n⁶·∏_m(−(2h_m+1))/(2n+2h_m−1) ≡ (−1)·1·(−1)⁶ = −1 (mod ℓ).
  This telescopes: Num(−1)/Num(0) = ∏_m(−½−h_m)/(n+h_m−½).
- **Log-derivatives.** With L_k := (log Γ_k)'(0) ∈ ℤ_(ℓ), shifting c ↦ c+1 in the numerator sum gives the exact identity

    L₀ − L₁ = 2/n − 2/(n−2) − 6(1+1/n) + Σ_m[2/(2h_m+1) + 2/(2n+2h_m−1)].

- **Reduction mod ℓ.** Since n ≡ 1 we get h_m ≡ x_m/40 and 2h_m+1 ≡ (x_m+20)/20, and x_m+20 ∈ {3, 21, 22, 23, 25, 26}
  are ℓ-units. So L₀ − L₁ ≡ 2 + 2 − 12 + 80T = K (mod ℓ).
- **Conclusion.** γ_{0,1} + γ_{1,1} = Γ₀(0)L₀ + Γ₁(0)L₁ ≡ Γ₀(0)·K (mod ℓ).
- In general form, K = 4 − 2a + 4Σ_m1/(1+2η_m), which is ≥ 4+2a by AM–HM. ∎

*Proof of Theorem A.* By Lemmas A2–A4,

  ρ₀ ≡ 168·ℓ^{−9}(γ_{0,1}+γ_{1,1}) ≡ 168·ℓ^{−9}·Γ₀·K (mod ℓ^{−8}).

Here 168 = 2³·3·7 and Γ₀ = Γ₀(0) are ℓ-units, and so is K, because ℓ ≥ 79 and ℓ ≠ 91079. The bounds for Z₇ and Z₉ are
Lemma A1(c). ∎

(91079 is prime and ≡ 39 mod 40. At n = 91080 the verifier's ℓ-adic engine finds v_ℓ(ρ₀) = −8, exactly the
non-generic case predicted by ℓ | K. That point is excluded from I.)

*Numerical confirmation.*
- **Exact runs.** For all 25 n ∈ I with n ≤ 3000 (verifier, `vx_exact.py`): v_ℓ(ρ₀) = −9, v_ℓ(c₃) = −2, v_ℓ(c₅) = 0, and
  ℓ⁹ρ₀ mod ℓ equals 168Γ₀K mod ℓ. The residues for n ≤ 1560 are identical to the prover's (43, 66, 167, 233, …).
- **ℓ-adic runs.** A generic ℓ-adic engine confirmed the same for all 243 n ∈ I in [3080, 40000] and 6 values above 91080.
- **Lemma-level checks.** Lemmas A1–A4 were checked exactly at n = 80, 200, 240, 360, 440, including the exact
  identities of Lemma A2.

*Corollary B (not needed below).* S_n ≠ 0 for all sufficiently large n ∈ I. This is unconditional but ineffective: it
uses the finite-dimensional ℚ-space of relations among 1, ζ₂(7), ζ₂(9). §8 gets nonvanishing directly instead.

---------------------------------------------------------------------------------------------------

## 8. L6 — proof of the Theorem, and the total margin — PROVED (given L1–L5)

**Proof of the Theorem.** Suppose, for contradiction, that ζ₂(7) = u/b and ζ₂(9) = w/b with u, w ∈ ℤ and b ∈ ℤ_{≥1}.
For n ∈ I define:
- D_n, the least positive odd integer with D_nρ₀, D_nZ₇, D_nZ₉ ∈ ℤ[½];
- e_n ≥ 0 such that a_{n,·} := 2^{e_n}D_n(ρ₀, Z₇, Z₉) ∈ ℤ³;
- M_n := max(|ρ₀|, |Z₇|, |Z₉|).

*Step 1 (a nonzero integer).* Put N_n := b·a_{n,0} + u·a_{n,1} + w·a_{n,2} ∈ ℤ. In ℚ₂, by L1, N_n = b·2^{e_n}D_n·S_n.
- Take n ∈ I with ℓ := n−1 > b.
- By Theorem A, v_ℓ(b·a_{n,0}) = v_ℓ(D_n) − 9, while v_ℓ(u·a_{n,1}) ≥ v_ℓ(D_n) − 3 and v_ℓ(w·a_{n,2}) ≥ v_ℓ(D_n) − 1.
  These use that ℓ ∤ b, that ℓ ∤ 2^{e_n}, and that D_n is an integer.
- By the ultrametric inequality v_ℓ(N_n) = v_ℓ(D_n) − 9 < ∞. So N_n ≠ 0, and in particular S_n ≠ 0.

*Step 2 (Liouville-type inequality).* A nonzero integer N satisfies |N|·|N|₂ ≥ 1. Here:
- |N_n| ≤ (b+|u|+|w|)·max_i|a_{n,i}| = (b+|u|+|w|)·2^{e_n}D_nM_n;
- |N_n|₂ = |b|₂·2^{−e_n}·|S_n|₂ ≤ 2^{−e_n}·2^{−v₂(S_n)}, because D_n is odd.

Hence, for all n ∈ I with n > b+1,

  1 ≤ (b+|u|+|w|) · D_n · M_n · 2^{−v₂(S_n)}.        (8.1)

The power of 2 has cancelled exactly, so only the odd part D_n matters.

*Step 3 (the right side of (8.1) tends to 0 along I).* For n ∈ I with n ≥ 2000:
- by L2 (Theorem D∞, valid along all n ≡ 0 mod 40, hence along I): log D_n ≤ (10 − R⁽⁰⁾)n + o(n);
- by L4 (Theorem G): log M_n ≤ −0.7812n − 4 log n + log(1.56·10¹²);
- by L3 (5.1): v₂(S_n)·log 2 ≥ 12n·log 2 − (1 + 10 log₂(1.3n))·log 2.

So the logarithm of the right side of (8.1) is at most

  n·(10 − R⁽⁰⁾ − 0.7812 − 12 log 2) + o(n) = −0.18909·n + o(n) → −∞

as n → ∞ in I. Since I is infinite (P6), this contradicts (8.1). ∎

*Remarks on the logic.*
- Step 1 is exactly condition 2 of [LS] Lemma 2.2 with ℓ(n) = n−1, and Steps 2–3 are [Lai] Lemma 2.1. Writing them out
  avoids any mismatch of hypotheses (e.g. "non-trivial forms", "ξ₀ ≠ 0").
- Only the residue-level bound of L2 is needed.
- L4 is needed only in the weak form g < −0.5921. L3 is needed only in the form 12n − O(log n).
- L5 is needed only for n ∈ I with n − 1 > b.

**The assembled total margin.** Replace R⁽⁰⁾ by the sharper values of L2⁺, and −0.7812 by g = −0.78127 (Theorem G′).
Then along I:

  limsup (1/n) log( max_i|a_{n,i}|·|L_n|₂ ) = limsup (1/n) log( D_n·M_n·2^{−v₂(S_n)} ) ≤ 10 − 12 log 2 + g − R.

| L2 level | R | L4 exponent g | total margin per n |
|---|---|---|---|
| residue (minimal route, §§4.1–4.5) | 1.0901241927613 | −0.78127 | −0.1891604 |
| + second-order lemma and switch | 1.2901241927613 | −0.78127 | −0.3891604 |
| + third-order row cancellation, X₁ = 11 | 1.4322937593059 | −0.78127 | −0.5313299 |
| **+ third order, X₁ = 41 (all proved ingredients)** | **1.4517049996220** | **−0.78127** | **−0.5507412** |
| same, with the numerical limit g* = −0.7812761397 | 1.4517049996220 | −0.7812761 | −0.5507473 |

The arithmetic is recomputed in `assembly/constants.out`, using 10 − 12 log 2 = 1.682233833280657.

**Finite-n illustration (NUMERICAL; not part of the proof).** n = 2000 and n = 2400 lie in I (1999 and 2399 are prime),
and there every ingredient is a proved per-n inequality:
- Theorem G, valid for n ≥ 2000;
- the per-prime procedure of Theorem D with the refinements of §4.6 (verifier's `dproc.py`);
- the bound (5.1).

Together they give

  (1/n)·log(max_i|a_{n,i}|·|L_n|₂) ≤ −0.7824 + 8.5730 − 8.2945 = −0.5039 (n = 2000),
                                    ≤ −0.7825 + 8.5580 − 8.2978 = −0.5223 (n = 2400).

With the true odd denominators instead (ln D_n/n = 8.5437, 8.5318) these become −0.533 and −0.548. The per-n bound
also gives the exponent of ℓ = n−1 in D_n as 9, which equals the truth and matches Theorem A.

The residue-level per-n bound, whose small-prime estimate is crude, gives ln D_n/n ≤ 9.433 and 9.386, i.e.
margins +0.356 and +0.306. So the minimal route is only asymptotically sufficient:
- the crude bound of Theorem D(b) costs 0.94 per n at n = 2000, against an asymptotic share of about 0.30;
- this cost decays only like n^{−1/2}: 0.14 at n = 10⁵ and 0.014 at n = 10⁷.

(`assembly/finite_n.json`.)

---------------------------------------------------------------------------------------------------

## 9. Compatibility audit: do the four gap proofs fit together?

**Rows 1–5 check the objects; rows 6–9 check how the tracks interlock.**

| item | GAP 1 growth | GAP 2 denominators | GAP 3 nonvanishing | GAP 4 valuation | assembled (§8) |
|---|---|---|---|---|---|
| family | (2t+n)∏(t+½−h_m)_{n+2h_m}/(t)_{n+1}^6 | same | same | general (a,j,δ); used with (6,3,1) | same |
| shifts | h = (n/40)(−17,1,2,3,5,6) | η = (−17,1,2,3,5,6)/40 (general lemmas for any η with Ση = 0, five η_m ≥ 0) | x = (−17,1,2,3,5,6), h = (n/40)x | any h ∈ ℤ⁶ with Σh = 0, N_m ≥ 0 | E |
| S_n | +∫R_n'''(t+½) | +∫ | +∫ | +∫R^{(j)} (j = 3) | +∫ |
| ρ₀ | Σ(i)₄r_{i,k}A_k^{(i+4)}, A_k = Σ_{l<k}(l+½)^{−s} | ΣX(k,l), l+½, 0 ≤ l < k | same ρ₀; X written with l−½, 1 ≤ l ≤ k (index shift by 1) | same | (3.3) |
| ζ-coefficients | "c₇" = −46080c₃, "c₉" = −860160c₅ | Z₇, Z₉ (same) | C₇, C₉ (same) | Z₇, Z₉ (same) | Z₇, Z₉ |
| admissible n | 40 \| n, n ≥ 2000 (G), n ≥ 10⁴ (G′) | every n ≡ 0 (mod 40) (Thm D); n → ∞ in 40ℤ (Thm D∞) | n ∈ I (40 \| n, n−1 prime, ≠ 91080) | every n | n ∈ I, n ≥ 2000, n−1 > b |
| what it delivers | log M_n ≤ −0.7812n + O(log n) | log D_n ≤ (10−R)n + o(n); q > n never divides D_n | v_ℓ(ρ₀) = −9 < v_ℓ(Z₇), v_ℓ(Z₉) | v₂(S_n) ≥ 12n − O(log n) | (8.1) |
| what it assumes from other gaps | nothing | nothing (its Cor. 3 quotes GAPs 1, 4) | nothing (its Cor. C quotes GAPs 1, 2, 4) | nothing | all four, only here |
| engines | lfam/veng; vexact; contour code | deng/lfam/veng; xeng; dproc; rzero | nv_indep/lfam; vx_exact; ℓ-adic engine | Mahler evaluator; vb.py; ledgers | constants.py, finite_n.py |

**Consistency checks made for this assembly.**
1. **Definitions.** The four definitions of ρ₀, and of the zeta coefficients up to naming, are literally identical.
   - The nonvanishing X(k,l) is the denominators' X(k,l−1).
   - The (8,3) draft's opposite sign (S_n = −∫) is not used anywhere.
   - All engines of all tracks agree on ρ₀, c₃, c₅ where they overlap. This includes E at n = 40 and 80 in every track.
2. **Index sets.** No gap needs a congruence or subsequence beyond 40 | n, except GAP 3, which needs n−1 prime. So I is
   admissible for all of them.
   - GAPs 1, 2 and 4 are proved for every (large) n ≡ 0 (mod 40), hence along I.
   - GAP 1's threshold n ≥ 2000 and GAP 3's condition n−1 > b only remove finitely many n.
3. **Denominators.**
   - The same D_n appears everywhere: the least odd common denominator.
   - Its 2-part is irrelevant. It cancels exactly in (8.1), as the valuation track showed and §8 Step 2 re-derives.
   - The ℓ⁹ required by Theorem A is automatically contained in D_n.
   - At ℓ = n−1 the denominator bound (f = 9 on (1, 20/17) at second order) is exactly sharp, by Theorem A.
4. **Growth.** GAP 1 bounds the same three numbers ρ₀, Z₇, Z₉ that GAP 2 clears and GAP 3 separates.
   - Its representation (6.1) involves ζ(7) and ζ(9) only as archimedean constants.
   - No 2-power normalisation of R_n is hidden anywhere: R_n has no factor 2^{12n}, unlike the LSZ normalisation.
   - So the rates add up as 10 − R (odd denominators) + g (sizes) − 12 log 2 (2-adic).
5. **Constants recomputed** (`assembly/constants.out`):
   - (i)₄, 46080, 860160, 45720, 858480;
   - a_μ(6) and β(6,3) = (0, −168, 168, −108, 48, −12);
   - K = 12386744/345345 and its factorisation, and that 91079 is prime and ≡ 39 (mod 40);
   - 10 − 12 log 2 and all margins and break-even values.
6. **R⁽⁰⁾ recomputed independently** (`assembly/rzero.py`): identical head rational and the same total to 22 digits.
7. **Residue-level bound vs. truth** (`assembly/resid_check.out`): 25 values of n up to 3200, every odd prime,
   0 violations, and no prime > n.
8. **Fully proved per-n bound at n ∈ I** (`assembly/finite_n.json`): at n = 2000 and 2400 it gives e^{−0.504n} and
   e^{−0.522n} (§8).
9. **Landscape certification without mpmath** (`assembly/cert3.py`, `cert3b.py`): all six inequalities of Lemma 7
   (standard and sharp) hold, and the negative controls fail. So Theorems G and G′, with their exponents −0.7812 and
   −0.78127, do not depend on mpmath. See §6.4.

---------------------------------------------------------------------------------------------------

## 10. Numerical verification inventory (exact rational arithmetic unless stated)

**GAP 1** (`pair79/growth/`, `pair79/verify-growth/`)

| file | checks | result |
|---|---|---|
| check_identities.py; vcontour.py | Prop. 3 vs exact c₃, c₅, ρ₀ (n = 40, 80) on 3 contours; negative control | rel. err. ≤ 3·10^{−41} (prover); 10^{−37}–10^{−43} at n = 40 and 10^{−18}–10^{−29} at n = 80, limited by quadrature (verifier); control fails as predicted |
| growth_check.py; vgrowth.py | contour values vs exact data (n = 120..640); rate up to n = 64000 | 6-digit agreement; −0.7818 at n = 64000 |
| certify.py, certify_sharp.py (mpmath.iv); vcertify.py (exact rational boxes) | Lemma 7, standard and sharp | ALL CERTIFIED (both methods) |
| validate_certify.py; vcert_validate.py | 12000 point tests; 2427 box tests; sensitivity controls | 0 violations |
| check_lemmas.py; vlemmas.py | Lemmas 4–6, kernel bounds, adversarial points (n up to 10⁴) | all hold; Lemma 4 error ≤ 0.136 vs 3.07 |
| explicit_constant.py; vconst.py | constants of Theorems G, G′ | 1.5548·10¹² ≤ 1.56·10¹²; 3.3070·10¹¹ ≤ 3.31·10¹¹ |
| saddles.py; vsaddle.py | saddle point τ*, Ψ(τ*) = −0.7812761397 | confirmed |

**GAP 2** (`pair79/denominators/`, `pair79/verify-denominators/`)

| file | checks | result |
|---|---|---|
| deng.py; xeng.py | exact engines vs lfam/veng | identical |
| truth.py → truth_E_*.json | true odd denominators, 25 values n = 40..3200 | e.g. ln D/n = 8.5437 (n = 2000) |
| checks/first.out, second_big.out; t_thm1bc.py | Theorem D(a),(b),(c) and second order vs truth | 0 violations |
| dproc.py, cmp_disc.py | per-prime procedure (third order) vs truth, n ≤ 1600 | 0 violations |
| t_lemmas.py | Lemmas D7 (all c), D8 (≈ 14000 pairs), D9, Prop. D10 (all criterion rows); 5 shift vectors | 0 failures |
| t_cont_truth.py | continuum f vs truth, 2081 large primes, n = 200..3200 | 0 violations |
| cint.py / pint.py; xcont.py / xint.py | R⁽⁰⁾, R⁽²⁾, R⁽³⁾ (exact heads plus digamma tails) | identical to 18+ digits |

**GAP 3** (`pair79/nonvanishing/`, `pair79/verify-nonvanishing/`)

| file | checks | result |
|---|---|---|
| nv_verify.py; vx_thmA.py | Lemmas A1–A4 and Theorem A, exact | 0 violations |
| nv_fast.py; vx_exact.py | Theorem A for all n ∈ I, n ≤ 3000 (exact) | v_ℓ(ρ₀) = −9, residue = 168Γ₀K |
| vx_ladic.py | Theorem A for all 243 n ∈ I in [3080, 40000] and 6 n > 91080; n = 91080 gives −8 | as predicted |
| nv_beta.py; vx_beta.py | β(a,j), K, 91079 | confirmed |
| margins_I.jsonl; vx_margin.jsonl | exact margins along I, n = 80..720: −1.057, −0.646, −0.695, −0.697, −0.666, −0.658, −0.696, −0.656 | S_n ≠ 0 at all of them |

**GAP 4** (`pair79/valuation/`, `pair79/verify-valuation/`)

| file | checks | result |
|---|---|---|
| g4lib.py (Mahler); vb.py (Bernoulli) | direct evaluation of S_n without partial fractions or ζ₂ | agree with ledgers |
| check_lemmas.py; t_lemmas.py | (D1)–(D4), Lemmas V1–V5, term decomposition | 0 failures |
| sweep_small/mid; t_sweep, t_extra | 2839 + 3265 cases | 0 violations; bound sometimes attained |
| check_linear_form.py; t_linform.py | L1 modulo 2^{v₂(S)+60} and 2^{449..1529}; ζ₂ computed two ways | holds |

**Assembly** (`pair79/assembly/`)

| file | checks | result |
|---|---|---|
| constants.py → constants.out | all small constants; margin arithmetic | as stated in §§0, 8 |
| rzero.py → rzero.out | third independent computation of R⁽⁰⁾; periodicity; constancy on steps | R⁽⁰⁾ = 1.090124192761300787 |
| resid_check.py → resid_check.out | Theorem D(a),(b),(c) vs true exponents, 25 values of n ≤ 3200; discrete ≤ continuum | 0 violations |
| disc_I.py → disc_I_2000.json, disc_I_2400.json | per-prime procedure at n = 2000, 2400 ∈ I (verifier's dproc) vs truth; exponent of ℓ = n−1 | 0 violations; E_ℓ = 9 = true |
| finite_n.py → finite_n.json | fully proved per-n criterion quantity at n = 2000, 2400 | e^{−0.504n}, e^{−0.522n} |
| cert3.py → cert3_weak_neg.json, cert3_mid.json | third, mpmath-free certification of Lemma 7 (own rational enclosures; per-term monotone extrema) | weak (P ≤ 0.9, Ψ ≤ −0.75) and mid (P ≤ 0.85, Ψ ≤ −0.78) sets CERTIFIED; controls fail |
| cert3b.py → cert3b_full.json, cert3b_sharp_neg.json | the same plus a centred mean-value bound near the saddle | all six inequalities of Lemma 7 (standard and sharp) CERTIFIED in ≤ 283 boxes each; control at −0.78126 fails |

Run everything from a short working directory (e.g. `C:\tmp`) with absolute paths, because of the Win32 path-length
limit. The assembly scripts import each other (`cert3b` imports `cert3`; `resid_check` and `finite_n` import `rzero`),
so copy `pair79/assembly/*.py` to a short directory such as `C:\tmp\asm` first. `resid_check.py` and `finite_n.py`
read the verifier's `truth_E_*.json` by absolute path.

---------------------------------------------------------------------------------------------------

## 11. Referee report on the assembled proof (the author as the harshest referee)

Each entry lists the issue, its severity **for the Theorem**, and the mitigation.

**A. Global**

- **A1. Nothing has been refereed by a human.**
  - The four gap proofs were written, and adversarially verified, by AI agents within one day.
  - The verification is extensive: independent re-derivations, independent code, negative controls. It is still no
    substitute for a human expert.
  - *Severity: fundamental.* The steps a human should re-derive first are listed in H.
- **A2. Errors of detail exist in the source texts, all caught by the verifiers and none load-bearing:**
  - the concavity interval in GAP 1 Lemma 8;
  - a sign typo in GAP 2 Lemma 3.2 (p₄ = +14);
  - an unjustified "k = n/2 dropped" clause in GAP 2 Theorem 1(c), which Theorem D(c) here repairs;
  - wrong sharpness or prefactor remarks.
  - Their existence means the remaining text may contain further slips.
  - *Severity: moderate.*
- **A3. Novelty.** The literature search recorded in `formalization.yaml` (2026-09-24) found no prior statement of the
  pair result, nor of {7, 9, 11}. The best published results found are Lai's {7, 9, 11, 13} (IJNT 2025) and ζ₂(5)
  (Calegari–Dimitrov–Tang; LSZ). Unrefereed GitHub drafts by C. D. Long (August 2026) claim that every ζ₂(s) with s
  odd and 3 ≤ s ≤ 29 is irrational, which would imply the pair result; we have not been able to verify their
  large-prime step. The search was not exhaustive (Google Scholar, MathSciNet and Lai's thesis were not searched); in
  particular the arithmetic-holonomy programme might give related results.
  - *Severity: none for correctness.*
- **A4. Dependence on preprints.** (P2) comes from LSZ (arXiv:2505.05005), but it is a two-line computation from the
  Hurwitz form of L₂(s, ω^{1−s}) and is reproduced in LSZ §2.3. It is also cross-checked numerically, with ζ₂ computed
  two independent ways to thousands of bits. Lai–Sprang's Lemma 2.2 is not used as a black box (§8 writes the argument
  out).
  - *Severity: low.*
- **A5. The assembly's own checks were not independently reviewed.** They were written in one session by the author
  of this document: `rzero.py`, `resid_check.py`, `cert3.py`, `cert3b.py`, `finite_n.py` and `constants.py`. They
  agree with the tracks' independent codes wherever they overlap: identical R⁽⁰⁾ head rational; the same true
  denominators; certification results consistent with both earlier certifications, including the locations where
  the negative controls fail. They add confidence but are not a substitute for review.
  - *Severity: low.*

**B. L4 (growth, GAP 1)**

- **B1. Computer-assisted inequalities.** Lemma 7 rests on two certifications with different bounding methods:
  - the prover's box enclosures (mpmath.iv, outward rounding);
  - the verifier's exact-rational boxes with harmonic-Taylor and monotone-corner bounds.
  - Both obtain the values of log and atan2 from mpmath.iv (on boxes in the first case, at rational points in the
    second). So they share one dependency: the correctness of mpmath.iv's elementary-function enclosures.
  - *Mitigation added in this assembly* (`assembly/cert3.py`, `cert3b.py`): a third certification.
    - It uses its own rational series enclosures (no mpmath, no floating point).
    - It uses a third bounding method: exact per-term extrema from two monotonicity facts, plus a centred
      mean-value bound near the saddle.
    - It certifies all six inequalities of Lemma 7 (standard and sharp), and the negative controls fail as they
      should.
    - What remains is trust in about 440 lines of new, self-contained code, short enough to audit by hand. No
      established library such as Arb has certified it.
  - *Severity: low for the Theorem.* It needs only g < −0.592 (residue route) or g < −0.2305 (full route), against the
    certified −0.7812 (all three certifications). The weakest mpmath-free set certified by per-term extrema alone
    already gives −0.75.
- **B2. The contour argument has many explicit pieces:** crossing segment, midpoint rule, the E_n bound, and
  Phragmén–Lindelöf. Each was re-derived by the verifier and stress-tested numerically. The analytic core, Prop. 3,
  needs ord_x R_n ≥ 5 at the half-integers in (0, n/40); this is exactly Lemma 0(b).
  - *Severity: low.*
- **B3. The value −0.78127 is an upper bound; the true limit is only numerically established.** Only the upper bound
  is used.
  - *Severity: none.*

**C. L2 (denominators, GAP 2)**

- **C1. The minimal route (residue level) uses:**
  - three short lemmas (D1, D2, and Theorem D(a) with the critical zeros);
  - the dictionary Lemma D3 and the generic-x Lemma D4;
  - an exact enumeration for R⁽⁰⁾.
  - R⁽⁰⁾ has three independent implementations (prover, verifier, assembly) with identical exact heads.
  - The tail ∫_{41}^∞ is evaluated with floating digamma at 30–40 digits, not interval arithmetic. This does not
    matter: periodicity and the exact finite computation min s = −2 give tail ≥ −2/41, hence
    R⁽⁰⁾ ≥ 1.0389 − 0.0488 = 0.990 > 0.901.
  - *Severity: low.*
- **C2. Lemma D4(iii)** (only non-candidate x are used; candidate primes are O(1) per candidate point) is argued, not
  formalised. It is cross-checked by the discrete ≤ continuum comparison at every large prime for 25 values of n
  (0 violations).
  - *Severity: low.*
- **C3. The o(n) of Theorem D∞ is ineffective** (PNT). The crude small-prime bound of Theorem D(b) costs 0.94 per n at
  n = 2000 and decays only like n^{−1/2}. So the minimal route cannot give an explicit n₀ below about 10⁵–10⁶ without
  explicit PNT bounds and better small-prime estimates.
  - *Severity: none for the qualitative Theorem.*
  - The sharper per-prime procedure already gives a negative fully proved value at n = 2000 and 2400.
- **C4. The headline margin −0.5507 depends on L2⁺.** L2⁺ consists of Prop. D10 (row cancellation), the continuum
  function f, and 1217 candidate intervals with an intricate soundness argument about unrealised point pieces. It was
  re-implemented by one independent verifier, and the continuum bound was never violated at 2081 large primes. But it
  is the most intricate new argument of the whole project.
  - *Severity: none for the Theorem.* The margin degrades gracefully: without Prop. D10 it is −0.389 (second order);
    without Lemma D5 as well it is −0.189.

**D. L5 (nonvanishing, GAP 3)**

- **D1. Elementary and fully written out.** The constants β₁ = −168 and K = 12386744/345345 were recomputed three
  times. The single excluded n = 91080 is harmless.
  - *Severity: low.*
- **D2. Ineffectivity in b** (the unknown denominator of the hypothetical rational values) is inherent in the method,
  as in [LS].
  - *Severity: none.*

**E. L3 (2-adic, GAP 4).** Elementary and sharp. No concern.

**F. L1.** Standard. Seven partial-fraction engines agree, and the form was checked end-to-end against two direct
Volkenborn evaluators. No concern.

**G. Assembly.** The objects, conventions and index sets were checked for mutual consistency (§9).
- **G1.** The assembly uses the four theorems only in the weak forms listed at the end of §8. Each has a large safety
  factor there:
  - g needs < −0.592 and has −0.781;
  - R needs > 0.901 and has 1.090 (residue route) or 1.452 (full route);
  - v₂ needs 12n − o(n) and has 12n − O(log n);
  - ℓ-separation needs any strict inequality and has 9 > 3.
- **G2.** The only non-textbook interplay between tracks is through the critical zeros (Lemma 0(b)), which three of
  the four tracks use: GAP 1 to cross the axis, GAP 2(a) to remove primes > n, GAP 3 for the two central zeros of
  order 6. Lemma 0(b) is elementary and was checked exactly.
- **G3. Single points of failure.** If any of the following were false, the proof would collapse.
  - **Theorem D(a).** Without it, primes in (n, 2.3n) could enter D_n with exponents up to 10, adding about 13 per n.
  - **Prop. 3 together with Lemma 7.** Without them only the naive residue bound, about +0.82 per n, is available, and
    the margin becomes positive.
  - **Theorem A.** Without it there is no nonvanishing.
  - **Theorem G4.** Without it there is no 2-adic smallness.
  - Each has been re-derived by an independent verifier and checked on exact data. Theorem D(a) held at all 25 values
    of n ≤ 3200 (no prime > n ever divides D_n), and Theorem A held for all n ∈ I up to 40000.
  - By contrast, L2⁺ (Lemma D5, Prop. D10, the continuum f) and the sharp constants of L4 are not single points of
    failure.

**H. What a human referee should re-derive first** (in order of importance for the minimal route):
1. Prop. 3 (all three identities, orientations, the role of ord ≥ 5) and the assembly of Theorem G. Then do one of:
   - audit the short mpmath-free certifier `assembly/cert3.py` + `cert3b.py`;
   - re-certify Lemma 7 with an established rigorous library such as Arb; a weak form (Ψ ≤ −0.75) suffices.
2. Theorem D(a) and (c), and the value R⁽⁰⁾ > 0.901 (about 100 lines of code: `assembly/rzero.py`).
3. Theorem A (Lemmas A1–A4) and the constants β₁ and K.
4. Theorem G4 (routine).
5. Only then, for the sharper margin: Lemma D5, Lemmas D7–D9, Prop. D10, and the continuum soundness argument.

**Verdict of this referee.** I found no gap in the logical chain from L0–L5 to the Theorem. The Theorem holds if the
four gap theorems hold, and they are needed only in forms with comfortable slack. The weakest links are the length and
novelty of the arguments (A1), not a specific step.
- The assembled total margin is **−0.5507 per n** with every proved ingredient.
- The minimal route needed for the Theorem has margin −0.189 per n, and it avoids the most intricate part (C4).

---------------------------------------------------------------------------------------------------

## 12. Remarks

1. **Why configuration E.**
   - Only two configurations have a proved growth rate: E, and F = (−0.5, 0.025, 0.0625, 0.1, 0.1375, 0.175) with
     80 | n, for which the growth track proves g ≤ −0.88. F's provable savings are only R⁽³⁾(X₁ = 11) ≈ 1.137, a margin
     of about −0.33, so E is the better of the two (−0.55).
   - Some configurations in the denominator track's batch have larger provable R⁽³⁾ (up to 1.65). Their growth rates
     are only measured, and would each need their own Lemma 7.
   - Configurations with a zero shift (A, B) have their growth pinned at φ(0) > −0.42, because W cannot cross the axis
     at a 5-fold zero on the positive side. So the "no zero shift" condition matters.
2. **Generality of the ingredients.**
   - GAP 4 holds for every admissible h and every (a, j, δ).
   - GAP 3's argument works for any even a, odd j and |η_m| < ½. The verifier showed that the critical-zero hypothesis
     is superfluous there.
   - GAP 2's lemmas hold for any η with Ση = 0 and at least j+2 = 5 nonnegative entries.
   - GAP 1's method applies to any configuration whose saddle and crossing values can be certified.
   - In particular GAP 3 gives an alternative nonvanishing route (along n = ℓ+1) for the unshifted (8,3) draft.
3. **Relation to the (8,3) draft.** If both are correct, the pair theorem implies the {7, 9, 11} theorem. The drafts
   use different nonvanishing mechanisms: the 2-adic dominant term there, ℓ = n−1 here. They also use different
   denominator mechanisms: Andrews there, Legendre counting and row cancellation here.
4. **A formal skeleton** (`pair79/integrator1/`) formalises the assembly in Lean, with the gap statements as hypotheses
   and with its own numerical parameters (g_E = −0.72, log D_n ≤ 9.0n). It was not re-checked here. The theorems proved
   here are stronger than those parameters (−0.78127 and 8.9099 respectively), but the exact Lean statements were not
   inspected. *(Editorial note, 2026-09-25: the Lean formalisation in this repository is now complete, with these
   parameters and no hypotheses; see `README.md`.)*
5. **Possible improvements** (not pursued):
   - use the third-order criterion beyond x = 41 (estimated +0.007 in R);
   - explicit PNT bounds, for an effective n₀;
   - a certification of Lemma 7 with Arb.
