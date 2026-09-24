"""Exact engine for p-adic Volkenborn linear forms from rational functions with poles on a lattice L*Z.

tau-picture:
    R(tau) = (2 tau + L n)^delta * prod_f prod_{m=m0_f}^{m0_f+len_f-1} (tau + b_f/d_f + m)^{e_f}  /  prod_{k=0}^{n} (tau + L k)^a
    S      = sum_{x in evals} int_{Z_p} R^{(j)}(tau + x) dtau          (evals = {b/p : 1<=b<=p-1}, equal weights)
With R = sum_{i,k} r_{i,k} (tau+Lk)^{-i}:
    int (tau + x + Lk)^{-m} = K_m(x) - m * sum_{l<Lk} (l+x)^{-m-1},   sum_x K_m(x) = m p^{m+1} zeta_p(m+1)  (0 for m odd)
    S = rho0 + sum_{m} C'_m zeta_p(m+1),  C'_m = m p^{m+1} (-1)^j sum_{i+j=m} (i)_j c_i,  c_i = sum_k r_{i,k}
    rho0 = -(-1)^j sum_{i,k} (i)_j (i+j) r_{i,k} sum_x H^{(x)}_{i+j+1}(Lk),  H^{(x)}_s(N) = sum_{l<N} (l+x)^{-s}
Partial fractions via Newton identities on power sums of reciprocal root offsets, all scaled by
Delta = lcm(1..X) so that everything is integral until the very end (fast, exact).
The p-adic value of S uses K_m computed by splitting Z_p into p^N residue classes + Bernoulli numbers.
"""
from fractions import Fraction as F
from math import comb, factorial, gcd, log
import sympy, pickle, os, time

HERE = os.path.dirname(os.path.abspath(__file__))

def lcm_upto(X):
    r = 1
    for q in sympy.primerange(2, X + 1):
        qq = q
        while qq * q <= X: qq *= q
        r *= qq
    return r

def vq(x, q):
    """q-adic valuation of int or Fraction"""
    if isinstance(x, F):
        if x == 0: return 10**9
        return vq(x.numerator, q) - vq(x.denominator, q)
    x = abs(x)
    if x == 0: return 10**9
    c = 0
    while x % q == 0: x //= q; c += 1
    return c

def rf(x, j):
    r = 1
    for l in range(j): r *= (x + l)
    return r

class Spec:
    """num: list of (b, d, m0, length, e) -> prod_{m=m0}^{m0+length-1}(tau + b/d + m)^e  (b/d not an integer)
       poles at tau=-L k, k=0..n, multiplicity a; delta: factor (2 tau + L n); evals: list of (b,p)"""
    def __init__(self, p, L, n, a, j, num, delta, evals, label=''):
        self.p, self.L, self.n, self.a, self.j = p, L, n, a, j
        self.num, self.delta, self.evals, self.label = num, delta, evals, label

def std_spec(p, L, n, e, j, delta, ext=0, label=None):
    """balanced symmetric family: numerator prod_{b=1}^{p-1} (tau + b/p - ext)_{L n + 2 ext}^e, a = (p-1) L e"""
    num = [(b, p, -ext, L * n + 2 * ext, e) for b in range(1, p)]
    a = (p - 1) * L * e
    evals = [(b, p) for b in range(1, p)]
    return Spec(p, L, n, a, j, num, delta, evals, label or 'p%d L%d e%d a%d j%d d%d ext%d' % (p, L, e, a, j, delta, ext))

def compute(spec, verbose=False):
    p, L, n, a, j = spec.p, spec.L, spec.n, spec.a, spec.j
    t0 = time.time()
    # ---- ranges of integer offsets u (root offsets = b/d + u) needed
    umax = 1
    for (b, d, m0, ln, e) in spec.num:
        umax = max(umax, abs(m0) + ln + L * n + 2)
    Umax = max(umax, L * n + 2)
    dmax = max([d for (b, d, m0, ln, e) in spec.num] + [x[1] for x in spec.evals] + [2])
    X = max(dmax * (Umax + 2), L * n + 2)
    Delta = lcm_upto(X)
    R_num = a - 1                  # power sums needed for Newton up to order a-1
    R_eval = a + j + 1             # H sums up to exponent a+j+1
    # ---- shift classes (b,d) needed for positive part and (d-b,d) for negative part
    classes = set()
    for (b, d, m0, ln, e) in spec.num:
        classes.add((b % d, d)); classes.add(((d - b) % d, d))
    # needed N values for prefix tables: for num factors: m0 - Lk + ln and m0 - Lk ... split at 0
    needN = {}
    def need(cls, N):
        needN.setdefault(cls, set()).add(N)
    for k in range(n + 1):
        for (b, d, m0, ln, e) in spec.num:
            lo, hi = m0 - L * k, m0 - L * k + ln
            bb = b % d; base = (b - bb) // d   # b/d = bb/d + base  -> shift u by base
            lo += base; hi += base
            if lo >= 0:
                need((bb, d), lo); need((bb, d), hi)
            elif hi <= 0:
                need(((d - bb) % d, d), -lo); need(((d - bb) % d, d), -hi)
            else:
                need(((d - bb) % d, d), -lo); need((bb, d), hi); need((bb, d), 0); need(((d - bb) % d, d), 0)
    # power-sum prefix tables A[cls][r][N] = sum_{u<N} (d*Delta/(b+d u))^r ; prefix products PP[cls][N]
    A = {}; PP = {}
    for cls, Ns in needN.items():
        bb, d = cls
        Ns = sorted(Ns); Nmax = Ns[-1]
        acc = [0] * (R_num + 1); prod_ = 1
        A[cls] = {}; PP[cls] = {}
        idx = 0
        for u in range(0, Nmax + 1):
            while idx < len(Ns) and Ns[idx] == u:
                A[cls][u] = acc[:]; PP[cls][u] = prod_; idx += 1
            if u == Nmax: break
            v = bb + d * u
            w = d * Delta // v
            pw = 1
            for r in range(1, R_num + 1):
                pw *= w; acc[r] += pw
            prod_ *= v
    # evaluation H tables at N = L k : Hh[s][k] = sum_x sum_{l<Lk} (d Delta/(b + d l))^s   (x=b/d)
    Hh = [[0] * (n + 1) for _ in range(R_eval + 1)]
    for (bx, dx) in spec.evals:
        acc = [0] * (R_eval + 1)
        for l in range(0, L * n + 1):
            if l % L == 0:
                k = l // L
                for s in range(R_eval + 1): Hh[s][k] += acc[s]
            if l == L * n: break
            v = bx + dx * l
            w = dx * Delta // v
            pw = 1
            for s in range(1, R_eval + 1):
                pw *= w; acc[s] += pw
    # pole harmonic prefix B[r][N] = sum_{v=1}^{N} (Delta/(L v))^r
    B = [[0] * (n + 1) for _ in range(R_num + 1)]
    acc = [0] * (R_num + 1)
    for v in range(0, n + 1):
        if v >= 1:
            w = Delta // (L * v); pw = 1
            for r in range(1, R_num + 1):
                pw *= w; acc[r] += pw
        for r in range(R_num + 1): B[r][v] = acc[r]
    fact = [factorial(i) for i in range(a + j + 3)]
    if verbose: print('tables %.1fs X=%d bits(Delta)=%d' % (time.time() - t0, X, Delta.bit_length()), flush=True)
    # ---- per pole (integer accumulation; common denominator Qden = prod_f d_f^(e_f*len_f) * (L^n n!)^a)
    Qden = 1
    for (b, d, m0, ln, e) in spec.num: Qden *= d ** (e * ln)
    Qden *= (L ** n * factorial(n)) ** a
    kfact = [factorial(i) for i in range(n + 1)]
    fa1 = fact[a - 1]
    c_int = [0] * (a + 1)      # c_i = c_int[i] / (Qden * fact[a-i] * Delta^(a-i))  -> scaled below
    rho_int = 0                # rho_acc = rho_int / (Qden * (a-1)! * Delta^(a+j+1))
    Dpow = [Delta ** m for m in range(a + j + 2)]
    for k in range(n + 1):
        S = [0] * (R_num + 1)
        Gnum = 1; sgn = 1
        for (b, d, m0, ln, e) in spec.num:
            lo, hi = m0 - L * k, m0 - L * k + ln
            bb = b % d; base = (b - bb) // d
            lo += base; hi += base
            cp, cn = (bb, d), ((d - bb) % d, d)
            if lo >= 0:
                for r in range(1, R_num + 1): S[r] += e * (A[cp][hi][r] - A[cp][lo][r])
                val = PP[cp][hi] // PP[cp][lo]
            elif hi <= 0:
                for r in range(1, R_num + 1): S[r] += e * (-1) ** r * (A[cn][-lo][r] - A[cn][-hi][r])
                val = PP[cn][-lo] // PP[cn][-hi]
                if (hi - lo) % 2: sgn = -sgn if e % 2 else sgn
            else:
                for r in range(1, R_num + 1): S[r] += e * ((-1) ** r * A[cn][-lo][r] + A[cp][hi][r])
                val = PP[cn][-lo] * PP[cp][hi]
                if (-lo) % 2 and e % 2: sgn = -sgn
            Gnum *= val ** e
        for r in range(1, R_num + 1): S[r] -= a * (B[r][n - k] + (-1) ** r * B[r][k])
        # pole part: 1/((-1)^k k!(n-k)! L^n)^a  -> times (L^n n!)^a gives binom(n,k)^a (-1)^{ka}
        Gnum *= comb(n, k) ** a
        if (k * a) % 2: sgn = -sgn
        zero_shift = False
        if spec.delta:
            c2 = L * (n - 2 * k)
            if c2 == 0:
                zero_shift = True; Gnum *= 2
            else:
                Gnum *= c2
                w = 2 * Delta // c2
                pw = 1
                for r in range(1, R_num + 1): pw *= w; S[r] += pw
        Gnum *= sgn
        E = [1] + [0] * R_num
        for m in range(1, R_num + 1):
            tot = 0
            for r in range(1, m + 1):
                tot += (-1) ** (r + 1) * S[r] * E[m - r] * (fact[m - 1] // fact[m - r])
            E[m] = tot
        if zero_shift:
            Em = [0] + [m * Delta * E[m - 1] for m in range(1, a)]
        else:
            Em = E[:a]
        T = 0
        for i in range(1, a + 1):
            mm = a - i
            num_i = Em[mm]
            if num_i == 0: continue
            # c_i contribution: Gnum*num_i/(Qden*fact[mm]*Delta^mm); bring to common scale fact[a-1]*Delta^(a-1)
            c_int[i] += Gnum * num_i * (fa1 // fact[mm]) * Dpow[a - 1 - mm]
            T += rf(i, j) * (i + j) * num_i * Hh[i + j + 1][k] * (fa1 // fact[mm])
        rho_int += Gnum * T
    c_acc = [F(0)] + [F(c_int[i], Qden * fa1 * Dpow[a - 1]) for i in range(1, a + 1)]
    rho_acc = F(rho_int, Qden * fa1 * Dpow[a + j + 1])
    rho0 = -(-1) ** j * rho_acc
    C = {}
    for i in range(1, a + 1):
        m = i + j
        if c_acc[i] != 0:
            C[m] = C.get(m, F(0)) + m * F(p) ** (m + 1) * (-1) ** j * rf(i, j) * c_acc[i]
    if verbose: print('coeffs %.1fs' % (time.time() - t0), flush=True)
    return dict(rho0=rho0, C=C, c=c_acc, secs=time.time() - t0)

# ---------------------------------------------------------------- p-adic constants
_bern = {}
def bern(r):
    if r not in _bern:
        b = sympy.bernoulli(r)
        if r == 1: b = sympy.Rational(-1, 2)
        _bern[r] = F(int(b.p), int(b.q))
    return _bern[r]

def Kconst(p, m, W, N=None):
    """Z = sum_{b=1}^{p-1} int_{Z_p} (tau + b/p)^{-m} dtau, returned as (U, s) with Z = U * p^s, U mod p^W (p-adic unit or not).
       Uses int f = p^{-N} sum_{c<p^N} int f(c + p^N u) du and Taylor/Bernoulli."""
    if N is None:
        N = 8 if p == 2 else (5 if p == 3 else 4)
    mod = p ** (W + 4)
    # (tau + b/p)^{-m} = p^m (b + p tau)^{-m};  int (b+p tau)^{-m} = p^{-N} sum_r binom(-m,r) p^{(N+1) r} B_r P_{m+r}(b)
    # terms have v_p >= (N+1) r - N - 1.  Want absolute precision p^{W - (N+1)}: r <= R
    R = (W + 2 * N + 4) // (N + 1) + 2
    tot = 0  # represents p^{N+1} * sum_b int (b+p tau)^{-m}  (integral)
    for b in range(1, p):
        invs = [pow(b + p * c, -1, mod) for c in range(p ** N)]
        # P_s = sum_c inv^s for s = m .. m+R
        pw = [pow(x, m, mod) for x in invs]
        for r in range(0, R + 1):
            Ps = sum(pw) % mod
            Br = bern(r)
            if Br != 0:
                # term = binom(-m,r) p^{(N+1)r} B_r P_s * p^{N+1} / p^{N} ... we accumulate p^{N+1}*int = p * sum binom p^{(N+1)r} B_r P
                num = (-1) ** r * comb(m + r - 1, r) * Br.numerator * p ** ((N + 1) * r + 1)
                den = Br.denominator
                # den has at most one factor p
                vp_den = 1 if den % p == 0 else 0
                den_u = den // (p ** vp_den)
                term = (num // (p ** vp_den)) * pow(den_u, -1, mod) * Ps
                tot = (tot + term) % mod
            pw = [(x * y) % mod for x, y in zip(pw, invs)]
    # Z = p^m * p^{-N-1} * tot
    return tot % (p ** W), m - N - 1

def padic_of_fraction(x, p, W, scale):
    """x * p^scale mod p^W as integer (requires v_p(x) >= -scale)"""
    num, den = x.numerator, x.denominator
    vd = vq(den, p)
    den_u = den // p ** vd
    s = scale - vd
    assert s >= 0, (scale, vd)
    return (num * p ** s * pow(den_u, -1, p ** W)) % (p ** W)

_Kcache = {}
def Kcached(p, m, W):
    key = (p, m)
    if key in _Kcache and _Kcache[key][2] >= W:
        U, s, W0 = _Kcache[key]
        return U % p ** W, s
    fn = os.path.join(HERE, 'Kcache_p%d_m%d.pkl' % (p, m))
    if os.path.exists(fn):
        U, s, W0 = pickle.load(open(fn, 'rb'))
        if W0 >= W:
            _Kcache[key] = (U, s, W0)
            return U % p ** W, s
    Wc = max(W, 2000)
    U, s = Kconst(p, m, Wc)
    _Kcache[key] = (U, s, Wc)
    try:
        pickle.dump((U, s, Wc), open(fn, 'wb'))
    except Exception:
        pass
    return U % p ** W, s

def vp_S(res, p, W_extra):
    """p-adic valuation of S = rho0 + sum_m C'_m zeta_p(m+1) where sum_x K_m = m p^{m+1} zeta_p(m+1) = U p^s.
    Returns (v, sigma, W): v=None means S == 0 mod p^(W-sigma)."""
    rho0, C = res['rho0'], res['C']
    terms = []
    sig = -vq(rho0, p) if rho0 != 0 else 0
    for m, cm in C.items():
        if m % 2 == 1 or cm == 0:
            continue
        x = cm / m
        terms.append((m, x))
    Nd = 8 if p == 2 else (5 if p == 3 else 4)
    for m, x in terms:
        sig = max(sig, -vq(x, p) - (m - Nd - 1) + m + 1)
    sig = max(sig, 0) + 5
    W = sig + W_extra
    mod = p ** W
    tot = padic_of_fraction(rho0, p, W, sig) if rho0 != 0 else 0
    for m, x in terms:
        U, s = Kcached(p, m, W + 10)
        assert s == m - Nd - 1
        e = sig + s - m - 1
        tx = padic_of_fraction(x, p, W, e)
        tot = (tot + tx * U) % mod
    if tot == 0:
        return None, sig, W
    return vq(tot, p) - sig, sig, W

def summarize(spec, res, p_prec=None, primes_detail=True):
    p, n, a, j, L = spec.p, spec.n, spec.a, spec.j, spec.L
    rho0, C = res['rho0'], res['C']
    live = {m: c for m, c in C.items() if m % 2 == 0 and c != 0}
    dead = {m: c for m, c in C.items() if m % 2 == 1 and c != 0}
    D = rho0.denominator
    for c in live.values():
        D = D * c.denominator // gcd(D, c.denominator)
    vpD = vq(D, p); Dp = D // p ** vpD
    def lnabs(x): return log(abs(x.numerator)) - log(x.denominator) if x != 0 else float('-inf')
    raw = max([lnabs(rho0)] + [lnabs(c) for c in live.values()])
    W_extra = p_prec or int(3 * a * n + 300)
    vS, sig, Wused = vp_S(res, p, W_extra)
    dn = int(sympy.ilcm(*range(1, n + 1))) if n > 1 else 1
    lndn = log(dn)
    out = dict(label=spec.label, n=n, consts=sorted(m + 1 for m in live), dead_odd=sorted(m + 1 for m in dead),
               vpS=vS, raw_n=raw / n, lnDp_n=log(Dp) / n, lndn_n=lndn / n,
               margin_n=(raw + log(Dp) - (vS if vS is not None else 0) * log(p)) / n,
               vpS_over_n=(vS / n if vS is not None else None))
    # prime-by-prime: exponent of q in D_p' vs d_n
    if primes_detail:
        rows = []
        for q in sympy.primerange(2, 3 * L * n * spec.p + 10):
            if q == p: continue
            e = vq(Dp, q)
            ed = vq(dn, q)
            if e == 0 and ed == 0: continue
            rows.append((int(q), ed, e))
        out['primes'] = rows
        out['max_exp_ratio'] = max((e / ed if ed else float('inf')) for (q, ed, e) in rows if e > 0) if rows else 0
        out['primes_gt_n'] = [(q, e) for (q, ed, e) in rows if q > n and e > 0]
    return out
