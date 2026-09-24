#!/usr/bin/env python3
"""Exact-arithmetic mirror of Zeta2Lean/Pair/Defs.lean and numerical checks of every statement in
Zeta2Lean/Pair/Statements.lean (the pair {zeta_2(7), zeta_2(9)}).  Pure standard library.

Every function below mirrors the Lean definition of the same name *literally* (rcoef is 0 outside
1<=i<=6, k<=n; offsets n h = Ico(-h, n+h) over Z; natural-number subtraction is truncated).
Power series are truncated mod eps^ORD (ORD = 7 covers every coefficient the statements use).

Optional independent cross-check: python/lfam_reference.py (verbatim copy of the exploration engine
lfam.py; a tiny stand-in for the two sympy functions it needs is installed if sympy is missing).

Usage:  python3 python/pair_mirror.py [--quick]
        (--quick: small n only, ~1 min;  full: adds config E at n = 120, 160 and lfam runs at
         n = 200, 400, a few minutes)
The 2-adic values J_s are read from python/zeta2_K17000.json (17000 bits), J_odd = 0.
"""
import sys, os, json, math, random, time
from fractions import Fraction as F
from math import comb, factorial, gcd, log

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
HERE = os.path.dirname(os.path.abspath(__file__))
QUICK = "--quick" in sys.argv
ORD = 7
FAILS = []
LOG2 = math.log(2)


def check(name, cond, info=""):
    if not cond:
        FAILS.append((name, info))
        print("  FAIL:", name, info, flush=True)
    return cond


def section(t):
    print("\n== " + t, flush=True)


# ----------------------------------------------------------------------------------------------
# valuations, primes
def v2int(x):
    x = abs(x)
    if x == 0:
        return 10 ** 9
    return (x & -x).bit_length() - 1


def vp(x, p):
    x = F(x)
    if x == 0:
        return 10 ** 9
    a, b, v = x.numerator, x.denominator, 0
    while a % p == 0:
        a //= p; v += 1
    while b % p == 0:
        b //= p; v -= 1
    return v


def is_int(x):
    return F(x).denominator == 1


def primes_upto(N):
    if N < 2:
        return []
    s = bytearray([1]) * (N + 1)
    s[0:2] = b"\x00\x00"
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(N + 1) if s[i]]


def lnabs(x):
    x = F(x)
    if x == 0:
        return float("-inf")
    return math.log(abs(x.numerator)) - math.log(x.denominator)


# ----------------------------------------------------------------------------------------------
# truncated power series over Q (lists of Fractions of length ORD)
def ps(c0=0, c1=0):
    z = [F(0)] * ORD
    z[0] = F(c0)
    z[1] = F(c1)
    return z


def ps_const(c):
    return ps(c, 0)


def ps_add(a, b):
    return [x + y for x, y in zip(a, b)]


def ps_scale(c, a):
    c = F(c)
    return [c * x for x in a]


def ps_mul(a, b):
    z = [F(0)] * ORD
    for i, x in enumerate(a):
        if x == 0:
            continue
        for j in range(ORD - i):
            if b[j]:
                z[i + j] += x * b[j]
    return z


def ps_inv(a):
    assert a[0] != 0, "inverse of series with zero constant term"
    z = [F(0)] * ORD
    z[0] = 1 / a[0]
    for m in range(1, ORD):
        s = F(0)
        for i in range(1, m + 1):
            s += a[i] * z[m - i]
        z[m] = -s / a[0]
    return z


def ps_pow(a, k):
    z = ps_const(1)
    for _ in range(k):
        z = ps_mul(z, a)
    return z


def int_linear_prod(factors):
    """prod (a + b eps) over integer pairs, truncated mod eps^ORD, integer coefficients"""
    z = [0] * ORD
    z[0] = 1
    for (a, b) in factors:
        for i in range(ORD - 1, 0, -1):
            z[i] = z[i] * a + z[i - 1] * b
        z[0] *= a
    return z


# ----------------------------------------------------------------------------------------------
# polynomials over Q (coefficient lists, low degree first)
def pl_mul(a, b):
    z = [F(0)] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                z[i + j] += x * y
    return z


def pl_add(a, b):
    n = max(len(a), len(b))
    return [(a[i] if i < len(a) else 0) + (b[i] if i < len(b) else 0) for i in range(n)]


def pl_trim(a):
    a = list(a)
    while a and a[-1] == 0:
        a.pop()
    return a


# ================================================================================================
# Pair/Defs.lean mirror
def Admissible(n, h):
    return (sum(h) == 0 and all(n + 2 * hm >= 0 for hm in h)
            and sum(1 for hm in h if hm >= 0) >= 5)


def offsets(n, hm):                    # Finset.Ico (-h) (n + h) over Z
    return range(-hm, n + hm)


def numSer(n, h, y):
    """prod_m prod_{u in offsets} (C(y + 1/2 + u) + X);  y rational.  Integer fast path:
    (y + 1/2 + u + eps) = ((2p + q + 2 q u) + 2 q eps) / (2 q) for y = p/q."""
    y = F(y)
    p, q = y.numerator, y.denominator
    facs = []
    for hm in h:
        for u in offsets(n, hm):
            facs.append((2 * p + q + 2 * q * u, 2 * q))
    z = int_linear_prod(facs)
    den = (2 * q) ** len(facs)
    return [F(c, den) for c in z]


_G = {}


def Gser(n, h, k):
    key = (n, tuple(h), k)
    if key not in _G:
        lin = ps(n - 2 * k, 2)
        num = numSer(n, h, F(-k))
        den = int_linear_prod([(j - k, 1) for j in range(n + 1) if j != k for _ in range(6)])
        _G[key] = ps_mul(ps_mul(lin, num), ps_inv([F(c) for c in den]))
    return _G[key]


def rcoef(n, h, i, k):
    if 1 <= i <= 6 and k <= n:
        return Gser(n, h, k)[6 - i]
    return F(0)


def genCsum(n, r, i):
    return sum((r(i, k) for k in range(n + 1)), F(0))


_A = {}


def Ahalf(k, s):                       # sum_{l<k} (l + 1/2)^{-s}
    key = (k, s)
    if key not in _A:
        _A[key] = F(0) if k == 0 else Ahalf(k - 1, s) + F(2, 2 * (k - 1) + 1) ** s
    return _A[key]


def genRho0(a, n, r):
    return -sum((F(i * (i + 1) * (i + 2) * (i + 3)) * r(i, k) * Ahalf(k, i + 4)
                 for i in range(1, a + 1) for k in range(n + 1)), F(0))


def genIntegrand(a, n, r, x):
    return sum((F(i * (i + 1) * (i + 2)) * r(i, k) * F(2, 2 * (x + k) + 1) ** (i + 3)
                for i in range(1, a + 1) for k in range(n + 1)), F(0))


def csum(n, h, i):
    return genCsum(n, lambda i_, k_: rcoef(n, h, i_, k_), i)


def rho0(n, h):
    return genRho0(6, n, lambda i_, k_: rcoef(n, h, i_, k_))


def Z7(n, h):
    return 46080 * csum(n, h, 3)


def Z9(n, h):
    return 860160 * csum(n, h, 5)


def integrand(n, h, x):
    return genIntegrand(6, n, lambda i_, k_: rcoef(n, h, i_, k_), x)


def Rnum(n, h):
    z = [F(n), F(2)]                                        # 2t + n
    for hm in h:
        for u in offsets(n, hm):
            z = pl_mul(z, [F(1, 2) + u, F(1)])
    return z


def PFpoly(n, h):
    tot = [F(0)]
    for i in range(1, 7):
        for k in range(n + 1):
            t = [rcoef(n, h, i, k)]
            for _ in range(6 - i):
                t = pl_mul(t, [F(k), F(1)])
            for j in range(n + 1):
                if j != k:
                    for _ in range(6):
                        t = pl_mul(t, [F(j), F(1)])
            tot = pl_add(tot, t)
    return tot


def Rser(n, h, y):
    y = F(y)
    lin = ps(2 * y + n, 2)
    den = ps_const(1)
    for j in range(n + 1):
        den = ps_mul(den, ps(y + j, 1))
    return ps_mul(ps_mul(lin, numSer(n, h, y)), ps_inv(ps_pow(den, 6)))


def dn(n):
    r = 1
    for p in primes_upto(n):
        q = p
        while q * p <= n:
            q *= p
        r *= q
    return r


def Dcrude(n):
    return 2 ** (6 * n) * factorial(n) ** 6 * dn(2 * n) ** 10


def ClearsDen(d, n, h):
    return d > 0 and is_int(d * rho0(n, h)) and is_int(d * Z7(n, h)) and is_int(d * Z9(n, h))


hE = [-17, 1, 2, 3, 5, 6]


def configE_n(m):
    return 40 * m


def configE_h(m):
    return [m * x for x in hE]


gE = -18 / 25
deltaE = 9.0


# ================================================================================================
# 2-adic helpers
def load_J(K=17000):
    """J_s mod 2^K for even s = 2..12 (a 2-adic integer), from the zeta_2 cache; J_odd = 0."""
    d = json.load(open(os.path.join(HERE, "zeta2_K17000.json")))
    J = {}
    for key, v in d.items():
        m = int(key); Z = int(v[0]); sh = int(v[1])
        s = m - 1
        e = v2int(s); so = s >> e
        assert e + m - sh == 0, (m, sh)
        J[s] = (Z * so) % (1 << K)
    for s in range(1, 14, 2):
        J[s] = 0
    return J


def scaled_mod(x, E, K):
    """x * 2^E mod 2^K as an integer (requires v2(x) >= -E)"""
    x = F(x)
    num, den = x.numerator, x.denominator
    vd = v2int(den)
    assert E - vd >= 0, (E, vd)
    return (num * pow(2, E - vd, 1 << K) * pow(den >> vd, -1, 1 << K)) % (1 << K)


def v2_linear_form(rho, coefs, J, K):
    """v2 of rho + sum_s coefs[s] J_s (J_s known mod 2^K); None if 0 mod 2^(K-E)."""
    E = 0
    for x in [rho] + list(coefs.values()):
        if x != 0:
            E = max(E, -vp(x, 2))
    MOD = 1 << K
    tot = scaled_mod(rho, E, K) if rho != 0 else 0
    for s, c in coefs.items():
        if c != 0:
            tot = (tot + scaled_mod(c, E, K) * J[s]) % MOD
    if tot == 0:
        return None
    return v2int(tot) - E


def v2S(n, h, J, K=17000, data=None):
    """v2 of S_n = rho0 + 60 c3 J6 + 210 c5 J8"""
    if data is None:
        data = (rho0(n, h), csum(n, h, 3), csum(n, h, 5))
    r, c3, c5 = data
    return v2_linear_form(r, {6: 60 * c3, 8: 210 * c5}, J, K)


def riemann_minus_value(n, h, N, J, K=4000):
    """v2( 2^{-N} sum_{x<2^N} integrand(x) - (rho0 + 60 c3 J6 + 210 c5 J8) ), computed mod 2^K.
    integrand(x) = sum_{i,k} (i)_3 r_{i,k} 2^{i+3} (2x+2k+1)^{-(i+3)}."""
    w = {}
    for i in range(1, 7):
        for k in range(n + 1):
            r = rcoef(n, h, i, k)
            if r != 0:
                w[(i, k)] = F(i * (i + 1) * (i + 2)) * r * F(2) ** (i + 3)
    rho, c3, c5 = rho0(n, h), csum(n, h, 3), csum(n, h, 5)
    E = max([0] + [-vp(x, 2) for x in list(w.values()) + [rho, c3, c5] if x != 0]) + N
    MOD = 1 << K
    wm = {key: scaled_mod(val, E - N, K) for key, val in w.items()}
    tot = 0
    for x in range(2 ** N):
        for (i, k), val in wm.items():
            tot += val * pow(2 * x + 2 * k + 1, -(i + 3), MOD)
    tot %= MOD                                   # = 2^E * R_N  (R_N = 2^{-N} sum)
    L = (scaled_mod(rho, E, K) + scaled_mod(60 * c3, E, K) * J[6] + scaled_mod(210 * c5, E, K) * J[8]) % MOD
    d = (tot - L) % MOD
    vL = v2_linear_form(rho, {6: 60 * c3, 8: 210 * c5}, J, K)
    return (None if d == 0 else v2int(d) - E), vL


def random_admissible(n, rng):
    """random admissible h for degree n (one negative shift at most)"""
    for _ in range(1000):
        h = [rng.randint(0, max(0, n // 3)) for _ in range(5)]
        neg = -sum(h)
        if n + 2 * neg >= 0:
            h.append(neg)
            rng.shuffle(h)
            if Admissible(n, h):
                return h
    return [0] * 6


# ================================================================================================
# GAP 1 heuristic: Stirling phase and its saddle points (architect's conjecture g = Re[phi + 2 pi i k tau])
def saddle_values(eta):
    """Points with exp(phi'(tau)) = 1 for phi(tau) = sum_m [F(tau+1+eta_m) - F(tau-eta_m)]
    - a [F(tau+1) - F(tau)], F(z) = z log z - z (principal branch).  Returns a list of
    (tau, k, Re[phi(tau) - 2 pi i k tau]) with phi'(tau) = 2 pi i k, upper half plane / real,
    tau > -1/2 (the rest are mirror images under tau -> -1 - tau)."""
    import cmath
    a = len(eta)

    def pmul(p, q):
        r = [0j] * (len(p) + len(q) - 1)
        for i, x in enumerate(p):
            for j, y in enumerate(q):
                r[i + j] += x * y
        return r
    P1, P2 = [1 + 0j], [1 + 0j]                      # coefficient lists, low degree first
    for e in eta:
        P1 = pmul(P1, [1 + e, 1]); P2 = pmul(P2, [-e, 1])
    for _ in range(a):
        P1 = pmul(P1, [0, 1]); P2 = pmul(P2, [1, 1])
    P = [x - y for x, y in zip(P1, P2)]
    while abs(P[-1]) < 1e-12 * max(abs(x) for x in P):
        P.pop()
    deg = len(P) - 1
    lead = P[-1]
    P = [x / lead for x in P]
    ev = lambda z: sum(c * z ** i for i, c in enumerate(P))
    roots = [(0.4 + 0.9j) ** i for i in range(deg)]  # Durand-Kerner
    for _ in range(2000):
        new = []
        for i, z in enumerate(roots):
            den = 1
            for j, w in enumerate(roots):
                if j != i:
                    den *= (z - w)
            new.append(z - ev(z) / den)
        roots = new
    Fz = lambda z: z * cmath.log(z) - z
    out = []
    for z in roots:
        if abs(z.imag) < 1e-9:
            z = complex(z.real, 1e-13)
        if z.imag < -1e-9 or z.real < -0.5 - 1e-9:
            continue
        if min(abs(z - x) for x in [0, -1] + list(eta) + [-1 - e for e in eta]) < 1e-9:
            continue
        dphi = sum(cmath.log(z + 1 + e) - cmath.log(z - e) for e in eta) - a * (cmath.log(z + 1) - cmath.log(z))
        phi = sum(Fz(z + 1 + e) - Fz(z - e) for e in eta) - a * (Fz(z + 1) - Fz(z))
        k = round(dphi.imag / (2 * math.pi))
        out.append((z, k, (phi - 2j * math.pi * k * z).real))
    return sorted(out, key=lambda t: (t[0].real, t[0].imag))


# ================================================================================================
def load_lfam():
    try:
        import sympy  # noqa: F401
    except ImportError:
        import types
        shim = types.ModuleType("sympy")
        shim.primerange = lambda a, b: [p for p in primes_upto(b - 1) if p >= a]

        def _ilcm(*args):
            r = 1
            for x in args:
                r = r * x // gcd(r, x)
            return r
        shim.ilcm = _ilcm
        sys.modules["sympy"] = shim
    sys.path.insert(0, HERE)
    import lfam_reference
    return lfam_reference


def lfam_run(lf, n, h):
    cnt = {}
    for hm in h:
        cnt[hm] = cnt.get(hm, 0) + 1
    num = [(1, 2, -hm, n + 2 * hm, e) for hm, e in sorted(cnt.items()) if n + 2 * hm > 0]
    spec = lf.Spec(2, 1, n, 6, 3, num, 1, [(1, 2)], "pair n=%d h=%s" % (n, h))
    res = lf.compute(spec)
    # lfam: S = +int R'''(t+1/2) = rho0_l + C[6] zeta(7) + C[8] zeta(9)  ->  ours = -(...)
    return dict(rho0=-res["rho0"], Z7=-res["C"].get(6, F(0)), Z9=-res["C"].get(8, F(0)),
                c=[F(0)] + [res["c"][i] for i in range(1, 7)], C=res["C"], secs=res["secs"])


def common_den(xs):
    D = 1
    for x in xs:
        d = F(x).denominator
        D = D * d // gcd(D, d)
    return D


def odd_part(D):
    while D % 2 == 0:
        D //= 2
    return D


# ================================================================================================
def main():
    t0 = time.time()
    rng = random.Random(20260924)
    J = load_J()
    small_n = list(range(0, 9)) if QUICK else list(range(0, 13))

    # ------------------------------------------------------------------ configurations
    section("Admissible / configE")
    for m in range(0, 31):
        check("configE adm m=%d" % m, Admissible(configE_n(m), configE_h(m)))
    check("hE sums to 0", sum(hE) == 0)
    print("  configE: n = 40m, h = m*(-17,1,2,3,5,6) admissible for m <= 30;  h/n =",
          [x / 40 for x in hE])
    cases = []                                    # (n, h) test cases for exact checks
    for n in small_n:
        cases.append((n, [0] * 6))
        for _ in range(2):
            cases.append((n, random_admissible(n, rng)))
    cases += [(4, [-1, 0, 0, 1, 0, 0]), (6, [-2, 0, 1, 0, 1, 0]), (10, [-4, 0, 1, 1, 2, 0])]
    cases = [(n, h) for (n, h) in cases if Admissible(n, h)]
    print("  %d exact test cases (n <= %d)" % (len(cases), max(n for n, _ in cases)))

    # ------------------------------------------------------------------ cross-check with lfam
    section("rcoef/rho0/Z7/Z9 (Lean definitions) vs lfam_reference.py (independent engine)")
    lf = None
    try:
        lf = load_lfam()
    except Exception as e:                       # pragma: no cover
        print("  (lfam_reference unavailable: %s)" % e)
    if lf is not None:
        xcases = cases + [(40, configE_h(1))] + ([] if QUICK else [(80, configE_h(2))])
        for (n, h) in xcases:
            d = lfam_run(lf, n, h)
            ok = (d["rho0"] == rho0(n, h) and d["Z7"] == Z7(n, h) and d["Z9"] == Z9(n, h)
                  and all(d["c"][i] == csum(n, h, i) for i in range(1, 7)))
            check("lfam n=%d h=%s" % (n, h), ok)
            only79 = sorted(m + 1 for m, c in d["C"].items() if c != 0)
            check("lfam constants n=%d h=%s" % (n, h), n == 0 or only79 in ([7, 9], [7], [9], []),
                  str(only79))
        print("  agree exactly on %d cases (incl. config E at n = 40%s); lfam's only live zeta values: 7, 9"
              % (len(xcases), "" if QUICK else ", 80"))

    # ------------------------------------------------------------------ Stmt_PF
    section("Stmt_PF: poly (Rnum = PFpoly) and series (Rser = sum r (y+k+eps)^-i)")
    for (n, h) in cases:
        if n <= 5:
            check("PF.poly n=%d h=%s" % (n, h), pl_trim(Rnum(n, h)) == pl_trim(PFpoly(n, h)))
    for (n, h) in cases:
        if n > 6:
            continue
        for _ in range(2):
            y = F(rng.randint(-40, 40), rng.randint(1, 9))
            if any(y + j == 0 for j in range(n + 1)):
                continue
            lhs = Rser(n, h, y)
            rhs = ps_const(0)
            for i in range(1, 7):
                for k in range(n + 1):
                    rhs = ps_add(rhs, ps_scale(rcoef(n, h, i, k), ps_inv(ps_pow(ps(y + k, 1), i))))
            check("PF.series n=%d h=%s y=%s" % (n, h, y), lhs == rhs)
    print("  PF.poly verified n <= 5; PF.series at random y, n <= 6")

    # ------------------------------------------------------------------ Stmt_CoeffVanish
    section("Stmt_CoeffVanish: symm, c1 = 0, c_even = 0")
    for (n, h) in cases + [(40, configE_h(1))]:
        for i in range(0, 8):
            for k in range(n + 1):
                check("symm n=%d h=%s i=%d k=%d" % (n, h, i, k),
                      rcoef(n, h, i, n - k) == (-1) ** (i + 1) * rcoef(n, h, i, k))
        check("c1 n=%d" % n, csum(n, h, 1) == 0)
        for i in range(0, 10, 2):
            check("ceven n=%d i=%d" % (n, i), csum(n, h, i) == 0)
    print("  verified on all cases + config E n = 40")

    # ------------------------------------------------------------------ Stmt_CrudeInt
    section("Stmt_CrudeInt: 2^{6n}(k!(n-k)!)^6 d_n^{6-i} r_{i,k} in Z;  ClearsDen(Dcrude n)")
    for (n, h) in cases + [(40, configE_h(1))]:
        d = dn(n)
        for i in range(1, 7):
            for k in range(n + 1):
                x = F(2) ** (6 * n) * (factorial(k) * factorial(n - k)) ** 6 * F(d) ** (6 - i) * rcoef(n, h, i, k)
                check("CrudeInt.coef n=%d h=%s i=%d k=%d" % (n, h, i, k), is_int(x))
        check("CrudeInt.forms n=%d h=%s" % (n, h), ClearsDen(Dcrude(n), n, h))
    print("  verified on all cases + config E n = 40")

    # ------------------------------------------------------------------ Stmt_IntegrandTaylor
    section("Stmt_IntegrandTaylor: integrand n h x = -6 [eps^3] Rser n h (x + 1/2)")
    for (n, h) in cases:
        if n > 6:
            continue
        for x in range(0, 4):
            check("IntegrandTaylor n=%d x=%d" % (n, x),
                  integrand(n, h, x) == -6 * Rser(n, h, F(2 * x + 1, 2))[3])
    print("  verified n <= 6, x <= 3")

    # ------------------------------------------------------------------ GenLinearForm, L1
    section("Stmt_GenLinearForm / Stmt_L1: Riemann sums -> rho0 + 60 c3 J6 + 210 c5 J8 (2-adically)")
    Nlev = 9 if QUICK else 12
    for (n, h) in [(0, [0] * 6), (1, [0] * 6), (2, [0, 0, 0, 0, 0, 0]), (4, [-1, 0, 0, 1, 0, 0]),
                   (6, [-2, 0, 1, 0, 1, 0])]:
        dv, vL = riemann_minus_value(n, h, Nlev, J)
        print("  n=%d h=%s: v2(S_n) = %s, v2(R_%d - S_n) = %s" % (n, h, vL, Nlev, dv))
        check("L1 n=%d h=%s" % (n, h), vL is not None and (dv is None or dv >= vL + Nlev - 12))
    # generic statement with a random coefficient array (a = 3; J_4 enters via i = 1, J_odd = 0)
    a, n = 3, 2
    rr = {(i, k): F(rng.randint(-9, 9), rng.randint(1, 5)) for i in range(1, a + 1) for k in range(n + 1)}
    r = lambda i, k: rr.get((i, k), F(0))
    MOD = 1 << 4000
    E = max(-vp(x, 2) for x in rr.values() if x != 0) + 20 + Nlev
    tot = 0
    for x in range(2 ** Nlev):
        tot += scaled_mod(genIntegrand(a, n, r, x), E - Nlev, 4000)
    val = scaled_mod(genRho0(a, n, r), E, 4000)
    for i in range(1, a + 1):
        val += scaled_mod(F(i * (i + 1) * (i + 2)) * genCsum(n, r, i), E, 4000) * J[i + 3]
    dv = v2int((tot - val) % MOD) - E
    print("  generic (a=3, n=2, random r): v2(R_%d - value) = %d" % (Nlev, dv))
    check("GenLinearForm random r", dv >= Nlev - 12)

    # ------------------------------------------------------------------ Stmt_Valuation (GAP 4)
    section("Stmt_Valuation (GAP 4): v2(S_n) >= 12n - A log2(n+1) - c")
    Ecases = [(40 * m, configE_h(m)) for m in (1, 2, 3)] + ([] if QUICK else [(160, configE_h(4))])
    worst = 0.0
    for (n, h) in cases + Ecases:
        if n == 0:
            continue
        v = v2S(n, h, J)
        check("S_n != 0 (n=%d h=%s)" % (n, h), v is not None)
        if v is None:
            continue
        deficit = 12 * n - v
        worst = max(worst, deficit / math.log2(n + 1))
        if n >= 40:
            print("  n=%d h=%s: v2(S_n) = %d, 12n - v2 = %d, /log2(n+1) = %.2f" % (n, h, v, deficit, deficit / math.log2(n + 1)))
    print("  max over tested (n,h) of (12n - v2(S_n))/log2(n+1) = %.2f   (statement: exists c, A)" % worst)
    check("Valuation with (A, c) = (8, 0) on tested cases", worst <= 8)

    # ------------------------------------------------------------------ GAP 1, 2, 3 data for E
    section("GAP data for configuration E (growth gE = %.2f, denominators deltaE = %.1f, nonvanishing)" % (gE, deltaE))
    rows = []
    for (n, h) in Ecases:
        rows.append((n, h, rho0(n, h), Z7(n, h), Z9(n, h)))
    if lf is not None and not QUICK:
        for m in (5, 10):
            n, h = 40 * m, configE_h(m)
            d = lfam_run(lf, n, h)
            rows.append((n, h, d["rho0"], d["Z7"], d["Z9"]))
    print("  n    raw/n (growth)  lnDodd/n (den)  maxexp(q>sqrt n)  v2S-12n   log(B*|L|_2)/n  S!=0")
    for (n, h, r0, z7, z9) in rows:
        raw = max(lnabs(r0), lnabs(z7), lnabs(z9)) / n
        D = common_den([r0, z7, z9])
        Do = odd_part(D)
        maxexp = max([vp(Do, q) for q in primes_upto(n) if q * q > n] + [0])
        big = [q for q in primes_upto(3 * n) if q > n and Do % q == 0]
        v = v2S(n, h, J, data=(r0, z7 / 46080, z9 / 860160))
        check("E: S_n != 0, n=%d" % n, v is not None)
        check("E: no prime > n in D, n=%d" % n, not big, str(big))
        check("E: ClearsDen(Dcrude) n=%d" % n, all(is_int(Dcrude(n) * x) for x in (r0, z7, z9)))
        a0, a1, a2 = D * r0, D * z7, D * z9
        B = abs(a0) + abs(a1) + abs(a2)
        vL = v + v2int(D)                        # |L|_2 = |D|_2 |S|_2
        crit = (lnabs(B) - vL * LOG2) / n
        print("  %-4d %+.4f         %.4f          %2d                %+5d     %+.4f          %s"
              % (n, raw, math.log(Do) / n, maxexp, v - 12 * n, crit, v is not None))
    print("  (growth and denominators are asymptotic statements; finite-n values are indicative only.")
    print("   exploration: raw/n -> about -0.786 (fits), provable residue-level lnDodd/n -> 10 - R_inf = 8.91;")
    print("   observed lnDodd/n is smaller (true denominators); the criterion quantity log(B|L|_2)/n < 0 is the margin)")

    section("Stmt_LaiSprangCond (sufficient for GAP 3): v_q(rho0) < v_q(Z7), v_q(Z9) at primes q in (sqrt n, n]")
    for (n, h, r0, z7, z9) in rows:
        ok = [q for q in primes_upto(n) if q * q > n and r0 != 0
              and (z7 == 0 or vp(r0, q) < vp(z7, q)) and (z9 == 0 or vp(r0, q) < vp(z9, q))]
        tot = [q for q in primes_upto(n) if q * q > n]
        gaps = sorted(set((vp(z7, q) - vp(r0, q), vp(z9, q) - vp(r0, q)) for q in tot))
        print("  n=%-4d %3d of %3d primes satisfy it; largest prime <= n: %d (%s); (v_q Z7 - v_q rho0, v_q Z9 - v_q rho0) in %s"
              % (n, len(ok), len(tot), tot[-1], "ok" if tot[-1] in ok else "FAILS", gaps[:6]))
        check("LaiSprang at largest prime <= n, n=%d" % n, tot[-1] in ok)

    section("GAP 1 heuristic: saddle points of the Stirling phase (architect's conjecture)")
    for name, eta, meas in (("E", [x / 40 for x in hE], "-0.786 (fit)"),
                            ("D {7,9,11}", [-0.4, -0.4, 0.05, 0.1, 0.1, 0.15, 0.2, 0.2], "-1.22 (n=650, rising)")):
        vals = saddle_values(eta)
        cand = [v for (z, k, v) in vals if z.real > 0]     # saddles right of the pole interval [-1, 0]
        for (z, k, v) in vals:
            print("  %-10s tau* = %+.6f%+.6fi  phi' = 2 pi i (%+d)  Re[phi - 2 pi i k tau] = %+.5f" % (name, z.real, z.imag, k, v))
        print("  %-10s conjectured growth rate (max over saddles with Re tau > 0): %+.5f   (measured %s)"
              % (name, max(cand), meas))
    check("saddle conjecture E below target gE",
          max(v for (z, k, v) in saddle_values([x / 40 for x in hE]) if z.real > 0) < gE)

    section("Margin arithmetic")
    print("  gE + deltaE = %.4f  <  12 log 2 = %.6f :  margin %.4f" % (gE + deltaE, 12 * LOG2, gE + deltaE - 12 * LOG2))
    check("marginE", gE + deltaE < 12 * LOG2)
    check("marginE via log_two_gt_d9", gE + deltaE < 12 * 0.6931471803)

    section("SUMMARY")
    print("  %d checks failed; %.0f s" % (len(FAILS), time.time() - t0))
    for f in FAILS[:20]:
        print("   ", f)
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
