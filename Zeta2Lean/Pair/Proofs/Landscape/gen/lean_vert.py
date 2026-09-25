"""Generate ../VertLine.lean: certificate for (L-iii)  Psi(eta) = Phi(7/100, eta) - 2 pi eta <= -18/25, 0 < eta <= 1.

Psi(y) = sum_j s_j Lf(a_j, y) - 2 pi y,  Lf(a, y) = a/2 log(a^2 + y^2) + y arctan(a/y) - a,
Psi'(y) = dPsi(y) = sum_j s_j arctan(a_j/y) - 2 pi.
On a cell [l, r]:  Psi(eta) <= Psi(l) + (r - l) M  with  M >= max(0, sup_(l,r) dPsi)  (mean value theorem);
each s_j arctan(a_j/zeta) is monotone in zeta, so the sup is bounded by its values at l or r
(at l = 0 by |arctan| < pi/2).  pi in [PI_LO, PI_HI] (Real.pi_gt_d20, Real.pi_lt_d20).

usage: python lean_vert.py          (writes ../VertLine.lean)
       python lean_vert.py search N (greedy cell search on the grid (1/N) Z)
"""
import os
import sys
from fractions import Fraction as Fr
from landscape_common import log_upper, log_lower, atan_upper, atan_lower

PI_LO = Fr(314159265358979323846, 10**20)
PI_HI = Fr(314159265358979323847, 10**20)
# summands of Psi in the order of its definition: (s_j, a_j)
A = [Fr(129, 200), Fr(99, 200), Fr(219, 200), Fr(9, 200), Fr(28, 25), Fr(1, 50), Fr(229, 200), Fr(-1, 200),
     Fr(239, 200), Fr(-11, 200), Fr(61, 50), Fr(-2, 25), Fr(107, 100), Fr(7, 100)]
S = [1, -1, 1, -1, 1, -1, 1, -1, 1, -1, 1, -1, -6, 6]
TERMS = list(zip(S, A))
GRID = [Fr(0), Fr(1, 50), Fr(1, 20), Fr(9, 50), Fr(1)]
TARGET = Fr(-18, 25)
DEC6 = 10**6


def ceil6(x): return Fr(-((-x.numerator*DEC6)//x.denominator), DEC6)
def ev_up(pc, c): return (PI_HI if pc > 0 else PI_LO)*pc + c


def lit(a):
    a = Fr(a)
    if a < 0: return "-(%s)" % lit(-a)
    if a.denominator == 1: return "%d" % a.numerator
    return "%d / %d" % (a.numerator, a.denominator)


def rnum(v): return "(%s : ℝ)" % lit(v)
def pi_expr(al, c): return "%s * π + %s" % (rnum(al), rnum(c))


class Cert:
    def __init__(self):
        self.lines = []; self.logf = {}; self.atf = {}; self.lff = {}; self.psi = {}

    def log_fact(self, Q, dirn):
        key = (Q, dirn)
        if key not in self.logf:
            name = "vl%d" % (len(self.logf) + 1)
            if dirn == 'up':
                b, t = log_upper(Q); stmt = "Real.log %s ≤ %s" % (rnum(Q), rnum(b))
            else:
                b, t = log_lower(Q); stmt = "%s ≤ Real.log %s" % (rnum(b), rnum(Q))
            self.lines.append("theorem %s : %s := by\n  have h := %s\n  linarith\n" % (name, stmt, t))
            self.logf[key] = (name, b)
        return self.logf[key]

    def at_fact(self, V, dirn):
        key = (V, dirn)
        if key not in self.atf:
            name = "va%d" % (len(self.atf) + 1)
            if dirn == 'up':
                al, c, t = atan_upper(V); stmt = "Real.arctan %s ≤ %s" % (rnum(V), pi_expr(al, c))
            else:
                al, c, t = atan_lower(V); stmt = "%s ≤ Real.arctan %s" % (pi_expr(al, c), rnum(V))
            self.lines.append("theorem %s : %s := by\n  have h := %s\n  linarith\n" % (name, stmt, t))
            self.atf[key] = (name, al, c)
        return self.atf[key]

    def lf_fact(self, s, a, y):
        """bound of Lf a y from above (s > 0) or below (s < 0) as P*pi + C"""
        key = (a, y)
        if key in self.lff: return self.lff[key]
        name = "vf%d" % (len(self.lff) + 1)
        dirn = 'up' if s > 0 else 'lo'
        ldir = 'up' if ((dirn == 'up') == (a > 0)) else 'lo'
        if y == 0:
            Q = a*a
            ln, lb = self.log_fact(Q, ldir)
            P = Fr(0); C = a/2*lb - a
            eq = "Lf_eq_zero (a := %s) (Q := %s) (by norm_num)" % (rnum(a), rnum(Q))
            deps = [ln]
        else:
            Q = a*a + y*y; sg = 1 if a > 0 else -1; V = abs(a)/y
            adir = 'up' if ((dirn == 'up') == (sg > 0)) else 'lo'
            ln, lb = self.log_fact(Q, ldir)
            an, al, ac = self.at_fact(V, adir)
            P = sg*y*al; C = a/2*lb + sg*y*ac - a
            eq = "%s (a := %s) (y := %s) (Q := %s) (V := %s) (by norm_num) (by norm_num)" % (
                "Lf_eq_pos" if sg > 0 else "Lf_eq_neg", rnum(a), rnum(y), rnum(Q), rnum(V))
            deps = [ln, an]
        stmt = ("Lf %s %s ≤ %s" % (rnum(a), rnum(y), pi_expr(P, C))) if dirn == 'up' else \
               ("%s ≤ Lf %s %s" % (pi_expr(P, C), rnum(a), rnum(y)))
        self.lines.append("theorem %s : %s := by\n  rw [%s]\n  linarith [%s]\n" % (name, stmt, eq, ", ".join(deps)))
        self.lff[key] = (name, P, C)
        return self.lff[key]

    def psi_fact(self, y):
        if y in self.psi: return self.psi[y]
        names = []; pc = Fr(0); c = Fr(0)
        for s, a in TERMS:
            n, P, C = self.lf_fact(s, a, y); names.append(n); pc += s*P; c += s*C
        pc -= 2*y
        B = ceil6(ev_up(pc, c))
        name = "psi_at_%d" % len(self.psi)
        self.lines.append("/-- `Ψ(%s) ≤ %s`. -/\ntheorem %s : Psi %s ≤ %s := by\n  unfold Psi\n  linarith [%s, Real.pi_gt_d20, Real.pi_lt_d20]\n"
                          % (lit(y), lit(B), name, rnum(y), rnum(B), ", ".join(names)))
        self.psi[y] = (name, B)
        return self.psi[y]


def dpsi_sup(cert, l, r):
    """(M, lean 'have' lines, fact names): M >= sup of dPsi on (l, r), before max with 0."""
    ds = []; deps = []; pc = Fr(-2); c = Fr(0)
    for s, a in TERMS:
        x = "Real.arctan (%s / ζ)" % lit(a)
        if s*a > 0:           # s_j arctan(a_j/zeta) decreasing: sup at l
            if l == 0:
                ds.append("have := Real.%s (%s / ζ)" % ("arctan_lt_pi_div_two" if a > 0 else "neg_pi_div_two_lt_arctan", lit(a)))
                pc += Fr(abs(s), 2); continue
            V = abs(a)/l
            an, al, ac = cert.at_fact(V, 'up')
            if a > 0:
                ds.append("have : %s ≤ Real.arctan %s := arctan_div_le_of_nonneg (by norm_num) (by norm_num) h1.le (by norm_num)" % (x, rnum(V)))
                pc += s*al; c += s*ac
            else:
                ds.append("have : -Real.arctan %s ≤ %s := arctan_div_ge_of_nonpos' (by norm_num) (by norm_num) h1.le (by norm_num)" % (rnum(V), x))
                pc += (-s)*al; c += (-s)*ac
            deps.append(an)
        else:                 # increasing: sup at r   (here a_j > 0 > s_j)
            assert a > 0 and s < 0
            V = a / r
            an, al, ac = cert.at_fact(V, 'lo')
            ds.append("have : Real.arctan %s ≤ %s := arctan_div_ge_of_nonneg (by norm_num) hζ h2.le (by norm_num)" % (rnum(V), x))
            pc += s*al; c += s*ac; deps.append(an)
    return ev_up(pc, c), ds, deps


def cell_bound(l, r):
    cert = Cert()
    _, B = cert.psi_fact(l)
    Mv, _, _ = dpsi_sup(cert, l, r)
    return B + (r - l)*max(ceil6(Mv), Fr(0))


def search(N, slack=Fr(1, 1000)):
    cells = []; k = 0
    while k < N:
        ok = None; step = 1
        while k + step <= N and cell_bound(Fr(k, N), Fr(k + step, N)) <= TARGET - slack:
            ok = k + step; step *= 2
        if ok is None: raise RuntimeError("no cell from %d/%d" % (k, N))
        bad = min(k + step, N + 1)
        while bad - ok > 1:
            mid = (ok + bad)//2
            if mid <= N and cell_bound(Fr(k, N), Fr(mid, N)) <= TARGET - slack: ok = mid
            else: bad = mid
        cells.append((k, ok)); k = ok
    return cells


HEADER = '''import Zeta2Lean.Pair.Proofs.Landscape.VertBase

/-!
# (L-iii) The vertical line through the saddle: `Ψ(η) = Φ(7/100, η) - 2πη ≤ -18/25`, `0 < η ≤ 1`

**Certificate** (generated by `Landscape/gen/lean_vert.py`, exact rational arithmetic): four cells
`[0, 1/50]`, `[1/50, 1/20]`, `[1/20, 9/50]`, `[9/50, 1]`.  On a cell `[l, r]`,
`Ψ(η) ≤ Ψ(l) + (r - l) M` (`Psi_le_of_deriv`), where `M ≥ sup_{(l, r)} Ψ'` comes from the
monotonicity in `ζ` of every summand `s_j arctan(a_j/ζ)` of `Ψ' = dPsi` (evaluated at `l` or `r`;
at `l = 0` by `|arctan| < π/2`).  The values `Ψ(l)` are bounded from the rational `log`/`arctan`
certificates of `Numerics.lean` (`Lf_eq_pos`, `Lf_eq_neg`, `Lf_eq_zero`), and `π` by
`Real.pi_gt_d20`, `Real.pi_lt_d20`.  True maximum: `-0.78127` at `η ≈ 0.031`.
-/

set_option linter.style.longLine false

open Real

noncomputable section

namespace Zeta2.Pair.Landscape

/-! ## Certified values of `log`, `arctan` and `Lf` at the grid points -/

'''


def generate(grid=GRID):
    cert = Cert(); cell_out = []; report = []
    cells = [(grid[i], grid[i + 1]) for i in range(len(grid) - 1)]
    for ci, (l, r) in enumerate(cells, 1):
        pn, B = cert.psi_fact(l)
        Mv, ds, deps = dpsi_sup(cert, l, r)
        M = max(ceil6(Mv), Fr(0))
        tot = B + (r - l)*M
        assert tot <= TARGET, (ci, float(tot))
        report.append((str(l), str(r), float(B), float(Mv), float(tot)))
        cell_out.append("/-- Cell `[%s, %s]`: `Ψ(l) ≤ %s`, `Ψ' ≤ %s`, bound `%.6f`. -/" % (lit(l), lit(r), lit(B), lit(M), float(tot)))
        cell_out.append("theorem vert_cell_%d : ∀ η, %s ≤ η → η ≤ %s → Psi η ≤ -18 / 25 := by" % (ci, rnum(l), rnum(r)))
        cell_out.append("  have hM : ∀ ζ, %s < ζ → ζ < %s → dPsi ζ ≤ %s := by" % (rnum(l), rnum(r), rnum(M)))
        cell_out.append("    intro ζ h1 h2")
        cell_out.append("    have hζ : 0 < ζ := by linarith")
        cell_out += ["    " + d for d in ds]
        cell_out.append("    unfold dPsi")
        cell_out.append("    linarith [%s]" % ", ".join(deps + ["Real.pi_gt_d20", "Real.pi_lt_d20"]))
        cell_out.append("  intro η h1 h2")
        cell_out.append("  have h := Psi_le_of_deriv (l := %s) (r := %s) (M := %s) (by norm_num) hM (by norm_num) η h1 h2"
                        % (rnum(l), rnum(r), rnum(M)))
        cell_out.append("  have hB := %s" % pn)
        cell_out.append("  linarith")
        cell_out.append("")
    fin = ["/-- **(L-iii)** `Φ(7/100, η) - 2πη ≤ -18/25` for `0 < η ≤ 1`, in the form `Ψ(η) ≤ -18/25`. -/",
           "theorem Psi_le : ∀ η ∈ Set.Ioc (0 : ℝ) 1, Psi η ≤ -18 / 25 := by",
           "  rintro η ⟨h1, h2⟩"]
    for ci, (l, r) in enumerate(cells, 1):
        if ci < len(cells):
            fin.append("  rcases le_or_gt η %s with c%d | c%d" % (rnum(r), ci, ci))
            fin.append("  · exact vert_cell_%d η (by linarith) c%d" % (ci, ci))
        else:
            fin.append("  exact vert_cell_%d η (by linarith) h2" % ci)
    fin.append("")
    out = HEADER + "\n".join(cert.lines) + "\n/-! ## The cells -/\n\n" + "\n".join(cell_out) + "\n".join(fin) + "\nend Zeta2.Pair.Landscape\n"
    return out, report, (len(cert.logf), len(cert.atf), len(cert.lff))


if __name__ == "__main__":
    if len(sys.argv) > 1 and sys.argv[1] == "search":
        print(search(int(sys.argv[2]) if len(sys.argv) > 2 else 100)); sys.exit(0)
    out, report, counts = generate()
    here = os.path.dirname(os.path.abspath(__file__))
    dest = sys.argv[1] if len(sys.argv) > 1 else os.path.join(here, "..", "VertLine.lean")
    with open(dest, "w", encoding="utf-8", newline="\n") as fh:
        fh.write(out)
    print("log/atan/Lf facts:", counts)
    for row in report: print(row)
