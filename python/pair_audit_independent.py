#!/usr/bin/env python3
"""audit_pair.py -- independent adversarial audit of Zeta2Lean/Pair/{Defs,Statements}.lean.

Stdlib only.  Shares NO code with python/pair_mirror.py, lfam.py or the verifier's veng.py.

  A. rcoef (Lean-literal Gser formula) are the partial-fraction coefficients of the PRODUCT form
     R_n(t) = (2t+n) prod_m (t+1/2-h_m)_{n+2h_m} / (t)_{n+1}^6: identity checked at random rational t
     (and at 6n+6 points = a complete proof for small n); Stmt_IntegrandTaylor checked exactly at
     config E n = 40 (x = 0, 1, 7) by an independent product-form Taylor expansion.
  B. J_s from Bernoulli moments with 2^NJ residue classes (independent of the zeta_2 cache), compared
     with python/zeta2_K17000.json; J_odd ~ 0.
  C. End-to-end L1: Riemann sums of -R_n'''(x+1/2) computed from the PRODUCT form (mod 2^K) converge
     2-adically to rho0 + 60 c3 J6 + 210 c5 J8 built from the Lean-literal rcoef/genRho0/genCsum.
  D. Stmt_Valuation uniformity: 12n - v2(S) over extreme admissible shift vectors.
  E. Gap statements at finite n along config E; fingerprints vs the verifier's E6.jsonl
     (optional: set VERIF_DIR to the verifier's folder containing E6.jsonl).
  F. Lai-Sprang condition at q = n - 1 prime (the recommended GAP 3 route).

Installed in the project as python/pair_audit_independent.py (audit of 2026-09-24).
usage: python3 python/pair_audit_independent.py [quick|full]     (quick ~15 s, full ~1 min)
"""
import sys, os, math, random, time, json
from fractions import Fraction as Fr

if hasattr(sys, "set_int_max_str_digits"):
    sys.set_int_max_str_digits(0)
MODE = sys.argv[1] if len(sys.argv) > 1 else "quick"
PAIR = os.environ.get("PAIR_ROOT", os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
VERIF = os.environ.get("VERIF_DIR", "")
FAILS = []
LOG2 = math.log(2)


def check(name, cond, info=""):
    if not cond:
        FAILS.append((name, info))
        print("  ** FAIL:", name, info, flush=True)
    return cond


def v2(x):
    x = Fr(x)
    if x == 0:
        return 10 ** 9
    a, b = abs(x.numerator), x.denominator
    return ((a & -a).bit_length() - 1) - ((b & -b).bit_length() - 1)


def vq(x, q):
    x = Fr(x)
    if x == 0:
        return 10 ** 9
    a, b, v = abs(x.numerator), x.denominator, 0
    while a % q == 0:
        a //= q; v += 1
    while b % q == 0:
        b //= q; v -= 1
    return v


def primes(N):
    s = bytearray([1]) * (N + 1)
    s[0:2] = b"\x00\x00"[: min(2, N + 1)]
    for i in range(2, int(N ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(N + 1) if s[i]]


def lnabs(x):
    x = Fr(x)
    return float("-inf") if x == 0 else math.log(abs(x.numerator)) - math.log(x.denominator)


# ------------------------------------------------------------------------------------------------
# admissibility (Lean: sum h = 0, n + 2h >= 0, #{h >= 0} >= 5)
def admissible(n, h):
    return len(h) == 6 and sum(h) == 0 and all(n + 2 * x >= 0 for x in h) and sum(1 for x in h if x >= 0) >= 5


def offsets(n, hm):  # Finset.Ico (-h) (n + h) over Z
    return list(range(-hm, n + hm))


# ------------------------------------------------------------------------------------------------
# A. Lean-literal rcoef: r_{6-mu,k} = [eps^mu] Gser n h k,
#    Gser = (C(n-2k) + 2X) * numSer n h (-k) * (prod_{j in range(n+1), j != k} (C(j-k)+X)^6)^{-1},
#    numSer n h y = prod_m prod_{u in offsets} (C(y + 1/2 + u) + X).
def lean_rcoef(n, h):
    offs = [u for hm in h for u in offsets(n, hm)]
    Nf = len(offs)
    L = 6
    r = {}
    for k in range(n + 1):
        num = [n - 2 * k, 2, 0, 0, 0, 0]              # (n - 2k + 2X), integer coefficients
        for u in offs:                                 # * (2(u-k)+1 + 2X), later / 2^Nf
            a0 = 2 * (u - k) + 1
            for d in range(L - 1, 0, -1):
                num[d] = num[d] * a0 + num[d - 1] * 2
            num[0] *= a0
        den = [1, 0, 0, 0, 0, 0]
        for j in range(n + 1):
            if j == k:
                continue
            c = j - k
            for _ in range(6):
                for d in range(L - 1, 0, -1):
                    den[d] = den[d] * c + den[d - 1]
                den[0] *= c
        inv = [Fr(0)] * L
        inv[0] = Fr(1, den[0])
        for d in range(1, L):
            inv[d] = -sum(den[e] * inv[d - e] for e in range(1, d + 1)) / den[0]
        G = [sum(num[e] * inv[d - e] for e in range(d + 1)) / (2 ** Nf) for d in range(L)]
        for i in range(1, 7):
            r[(i, k)] = G[6 - i]
    return r


def csum(r, n, i):
    return sum((r.get((i, k), Fr(0)) for k in range(n + 1)), Fr(0))


def rho0_of(r, n):
    """-sum_{i=1..6} sum_{k<=n} (i)_4 r_{i,k} A_k^{(i+4)},  A_k^{(s)} = sum_{l<k} (l+1/2)^{-s}.
    Evaluated as -sum_i (i)_4 sum_l (l+1/2)^{-(i+4)} * (sum_{k>l} r_{i,k})  (swapped order)."""
    tot = Fr(0)
    for i in range(1, 7):
        suf = Fr(0)
        acc = Fr(0)
        for l in range(n - 1, -1, -1):        # l = n-1 .. 0; suffix sum over k in (l, n]
            suf += r[(i, l + 1)]
            if suf:
                acc += suf * Fr(2, 2 * l + 1) ** (i + 4)
        tot += i * (i + 1) * (i + 2) * (i + 3) * acc
    return -tot


def R_product(n, h, t):
    t = Fr(t)
    val = 2 * t + n
    for hm in h:
        for u in offsets(n, hm):
            val *= t + Fr(1, 2) + u
    den = Fr(1)
    for j in range(n + 1):
        den *= t + j
    return val / den ** 6


def PF_value(r, n, t):
    t = Fr(t)
    return sum((r[(i, k)] / (t + k) ** i for i in range(1, 7) for k in range(n + 1) if r[(i, k)]), Fr(0))


def taylor_product_form(n, h, y, L=4):
    """exact Taylor coefficients of R_n(y + eps), eps^0..eps^{L-1}, from the product form"""
    ser = [Fr(2 * y + n), Fr(2)] + [Fr(0)] * (L - 2)

    def mul_lin(s, c):     # s * (c + eps)
        return [s[d] * c + (s[d - 1] if d else 0) for d in range(L)]
    for hm in h:
        for u in offsets(n, hm):
            ser = mul_lin(ser, Fr(y) + Fr(1, 2) + u)
    den = [Fr(1)] + [Fr(0)] * (L - 1)
    for j in range(n + 1):
        for _ in range(6):
            den = mul_lin(den, Fr(y) + j)
    inv = [Fr(0)] * L
    inv[0] = 1 / den[0]
    for d in range(1, L):
        inv[d] = -sum(den[e] * inv[d - e] for e in range(1, d + 1)) / den[0]
    return [sum(ser[e] * inv[d - e] for e in range(d + 1)) for d in range(L)]


def lean_integrand(r, n, x):
    return sum((Fr(i * (i + 1) * (i + 2)) * r[(i, k)] * Fr(2, 2 * (x + k) + 1) ** (i + 3)
                for i in range(1, 7) for k in range(n + 1) if r[(i, k)]), Fr(0))


# ------------------------------------------------------------------------------------------------
# B. J_s = int_{Z_2} (t+1/2)^{-s} dt via 2^NJ classes + Bernoulli moments:
#    J_s = 2^{-NJ} sum_{a<2^NJ} sum_j C(-s,j) 2^{NJ j} B_j (a+1/2)^{-s-j},  (a+1/2)^{-e} = 2^e (2a+1)^{-e}
def bernoulli_upto(M):
    """B_0..B_M (B_1 = -1/2) via tangent numbers (Brent-Harvey)"""
    kmax = M // 2 + 1
    T = [0] * (kmax + 1)
    T[1] = 1
    for k in range(2, kmax + 1):
        T[k] = (k - 1) * T[k - 1]
    for k in range(2, kmax + 1):
        for j in range(k, kmax + 1):
            T[j] = (j - k) * T[j - 1] + (j - k + 2) * T[j]
    B = {0: Fr(1), 1: Fr(-1, 2)}
    for k in range(1, kmax + 1):
        B[2 * k] = Fr((-1) ** (k - 1) * 2 * k * T[k], 4 ** k * (4 ** k - 1))
    for j in range(3, 2 * kmax + 1, 2):
        B[j] = Fr(0)
    return B


def J_bernoulli(svals, K, NJ=10):
    """returns {s: (Jscaled, NJ)} with J_s = Jscaled * 2^{-NJ}, Jscaled mod 2^(K+NJ)"""
    KK = K + NJ + 16
    MOD = 1 << KK
    jmax = (KK + 40) // (NJ + 1) + 2          # term j has v2 >= (NJ+1) j + s - 1 (scaled by 2^NJ)
    B = bernoulli_upto(jmax + 2)
    emax = max(svals) + jmax
    P = [0] * (emax + 1)                        # P_e = sum_a (2a+1)^{-e} mod 2^KK
    for a in range(1 << NJ):
        iv = pow(2 * a + 1, -1, MOD)
        p = 1
        for e in range(emax + 1):
            P[e] = (P[e] + p) % MOD
            p = p * iv % MOD
    out = {}
    for s in svals:
        tot = 0
        for j in range(0, jmax + 1):
            b = B[j]
            if b == 0:
                continue
            bn, bd = b.numerator, b.denominator
            vd = (bd & -bd).bit_length() - 1
            bo = bd >> vd
            ex = NJ * j + s + j - vd
            assert ex >= 0
            cneg = (-1) ** j * math.comb(s + j - 1, j) if j > 0 else 1   # C(-s, j)
            tot += cneg * bn * pow(2, ex, MOD) * pow(bo, -1, MOD) * P[s + j]
        out[s] = (tot % MOD, NJ)
    return out


def J_cache(K):
    fn = os.path.join(PAIR, "python", "zeta2_K17000.json")
    d = json.load(open(fn))
    J = {}
    for key, v in d.items():
        m = int(key); Z = int(v[0]); sh = int(v[1]); s = m - 1
        if 1 <= s <= 12:
            J[s] = Fr(s) * Fr(2) ** m * Fr(Z) / Fr(2) ** sh      # J_{m-1} = (m-1) 2^m zeta_2(m)
    return J


def to_mod(x, E, K):
    """x * 2^E mod 2^K (requires v2(x) >= -E)"""
    x = Fr(x)
    if x == 0:
        return 0
    num, den = x.numerator, x.denominator
    vd = (den & -den).bit_length() - 1
    assert E - vd >= 0, (E, vd)
    return num * pow(2, E - vd, 1 << K) * pow(den >> vd, -1, 1 << K) % (1 << K)


def v2mod(U, E, K):
    """valuation of U * 2^{-E} where U mod 2^K; None if U == 0 mod 2^K"""
    U %= (1 << K)
    if U == 0:
        return None
    return ((U & -U).bit_length() - 1) - E


def v2_S(rho, c3, c5, Jb, K):
    """v2(rho + 60 c3 J6 + 210 c5 J8), J from Jb = {s: (Jscaled, NJ)}"""
    NJ = Jb[6][1]
    E = max([0] + [-v2(x) for x in (rho, 60 * c3, 210 * c5) if x != 0]) + NJ
    U = (to_mod(rho, E, K) + to_mod(60 * c3, E - NJ, K) * Jb[6][0] + to_mod(210 * c5, E - NJ, K) * Jb[8][0]) % (1 << K)
    v = v2mod(U, E, K)
    return v, K - E          # (valuation or None, absolute precision)


# ------------------------------------------------------------------------------------------------
# C. product-form Riemann sums of f(x) = -R'''(x+1/2) mod 2^K:
#    R(x+1/2+eps) = 2^{6n+6} (2x+1+n+2eps) prod_{m,u} (x+1+u+eps) prod_j (2x+2j+1+2eps)^{-6}
def riemann_product(n, h, N, K):
    MOD = 1 << K
    msk = MOD - 1
    offs = [u for hm in h for u in offsets(n, hm)]
    T = 0
    for x in range(1 << N):
        s0, s1, s2, s3 = (2 * x + 1 + n) & msk, 2, 0, 0
        for u in offs:
            c = x + 1 + u
            s0, s1, s2, s3 = (s0 * c) & msk, (s1 * c + s0) & msk, (s2 * c + s1) & msk, (s3 * c + s2) & msk
        d0, d1, d2, d3 = 1, 0, 0, 0
        for j in range(n + 1):
            c = 2 * x + 2 * j + 1
            d0, d1, d2, d3 = (d0 * c) & msk, (d1 * c + 2 * d0) & msk, (d2 * c + 2 * d1) & msk, (d3 * c + 2 * d2) & msk
        # d^6
        def mul(a, b):
            return ((a[0] * b[0]) & msk, (a[0] * b[1] + a[1] * b[0]) & msk,
                    (a[0] * b[2] + a[1] * b[1] + a[2] * b[0]) & msk,
                    (a[0] * b[3] + a[1] * b[2] + a[2] * b[1] + a[3] * b[0]) & msk)
        d = (d0, d1, d2, d3)
        d2_ = mul(d, d); d3_ = mul(d2_, d); d6 = mul(d3_, d3_)
        i0 = pow(d6[0], -1, MOD)
        i1 = (-d6[1] * i0 * i0) & msk
        i2 = (-(d6[1] * i1 + d6[2] * i0) * i0) & msk
        i3 = (-(d6[1] * i2 + d6[2] * i1 + d6[3] * i0) * i0) & msk
        c3 = (s0 * i3 + s1 * i2 + s2 * i1 + s3 * i0) & msk
        T += -6 * c3
    T = (T * pow(2, 6 * n + 6, MOD)) % MOD
    return T                                   # R_N = T * 2^{-N}


# ------------------------------------------------------------------------------------------------
def main():
    t0 = time.time()
    rng = random.Random(424242)
    FULL = MODE == "full"

    print("== A. rcoef (Lean-literal) = partial fractions of the product form", flush=True)
    small = []
    for n in range(0, 9):
        small.append((n, [0] * 6))
        for _ in range(3):
            for _t in range(200):
                neg = -rng.randint(0, n // 2)
                rest = [0] * 5
                budget = -neg
                for _b in range(budget):
                    rest[rng.randrange(5)] += 1
                h = rest + [neg]
                rng.shuffle(h)
                if admissible(n, h):
                    small.append((n, h))
                    break
    small += [(8, [-4, 4, 0, 0, 0, 0]), (8, [-4, 0, 0, 0, 0, 4]), (6, [-3, 1, 1, 1, 0, 0]), (7, [-3, 3, 0, 0, 0, 0])]
    nfull = 0
    for (n, h) in small:
        assert admissible(n, h), (n, h)
        r = lean_rcoef(n, h)
        # complete proof: numerator of the difference has degree <= 6n+5 -> 6n+6 non-pole zeros suffice
        pts = [Fr(2 * p + 1, 3) for p in range(6 * n + 6)]
        ok = all(R_product(n, h, t) == PF_value(r, n, t) for t in pts if all(t + j != 0 for j in range(n + 1)))
        check("PF identity (complete, 6n+6 points) n=%d h=%s" % (n, h), ok)
        nfull += 1
    print("  complete verification R_n = sum r (t+k)^-i on %d small admissible (n,h)" % nfull)
    hE = [-17, 1, 2, 3, 5, 6]
    big = [(40, hE), (20, [-10, 10, 0, 0, 0, 0]), (24, [-12, 2, 2, 2, 3, 3])]
    if FULL:
        big += [(80, [2 * x for x in hE])]
    RC = {}
    for (n, h) in big:
        r = lean_rcoef(n, h)
        RC[(n, tuple(h))] = r
        for _ in range(3):
            t = Fr(rng.randint(-10 ** 6, 10 ** 6), rng.randint(1, 10 ** 6))
            if any(t + j == 0 for j in range(n + 1)):
                continue
            check("PF identity n=%d h=%s t=%s" % (n, h, t), R_product(n, h, t) == PF_value(r, n, t))
    print("  random-point identity n = %s ok" % [n for n, _ in big])
    for (n, h) in big[:3]:
        r = RC[(n, tuple(h))]
        d = math.lcm(*range(1, n + 1))
        ok = all((Fr(2) ** (6 * n) * (math.factorial(k) * math.factorial(n - k)) ** 6 * Fr(d) ** (6 - i)
                  * r[(i, k)]).denominator == 1 for i in range(1, 7) for k in range(n + 1))
        check("CrudeInt.coef n=%d h=%s" % (n, h), ok)
        ok = all(r[(i, n - k)] == (-1) ** (i + 1) * r[(i, k)] for i in range(1, 7) for k in range(n + 1))
        check("CoeffVanish.symm n=%d h=%s" % (n, h), ok)
        check("CoeffVanish.c1/ceven n=%d h=%s" % (n, h), all(csum(r, n, i) == 0 for i in (1, 2, 4, 6)))
    print("  CrudeInt.coef, parity lemma, c1 = c2 = c4 = c6 = 0 at n = %s" % [n for n, _ in big[:3]])
    # Stmt_IntegrandTaylor exactly at config E n = 40
    r40 = RC[(40, tuple(hE))]
    for x in (0, 1, 7):
        tay = taylor_product_form(40, hE, Fr(2 * x + 1, 2))
        check("IntegrandTaylor n=40 x=%d" % x, lean_integrand(r40, 40, x) == -6 * tay[3])
    print("  Stmt_IntegrandTaylor exact at config E n=40, x = 0, 1, 7")
    # parity lemma / c1 / c_even at config E n = 40
    ok = all(r40[(i, 40 - k)] == (-1) ** (i + 1) * r40[(i, k)] for i in range(1, 7) for k in range(41))
    check("CoeffVanish.symm n=40 E", ok)
    check("CoeffVanish.c1/ceven n=40 E", all(csum(r40, 40, i) == 0 for i in (1, 2, 4, 6)))
    check("c3, c5 != 0 at n=40 E", csum(r40, 40, 3) != 0 and csum(r40, 40, 5) != 0)
    # deg R = -5 relations beyond c1 (sanity: expansion at infinity has no t^-1..t^-4 terms)
    t = Fr(10 ** 30)
    val = R_product(40, hE, t)
    check("deg R_n = -5 (t^5 R(t) -> finite nonzero)", 1.9 < float(val * t ** 5) < 2.1, float(val * t ** 5))

    print("\n== B. J_s from Bernoulli moments vs zeta2 cache", flush=True)
    NMAX = 160 if FULL else 120
    KJ = 26 * NMAX + 400                       # J precision (bits) for S up to n = NMAX
    Jb = J_bernoulli([3, 4, 5, 6, 7, 8, 9, 10], KJ)
    Jc = J_cache(KJ)
    for s in (4, 6, 8, 10):
        U, NJ = Jb[s]
        diff = (U - to_mod(Jc[s], NJ, KJ + NJ + 16)) % (1 << (KJ + NJ + 16))
        dv = v2mod(diff, NJ, KJ + NJ + 16)
        check("J_%d Bernoulli == cache" % s, dv is None or dv >= KJ - 10, dv)
        print("  J_%d: v2 = %s, agreement with cache to >= %s bits" % (s, v2mod(U, NJ, KJ + NJ), "all" if dv is None else dv))
    for s in (3, 5, 7, 9):
        U, NJ = Jb[s]
        vv = v2mod(U, NJ, KJ + NJ + 16)
        check("J_%d ~ 0" % s, vv is None or vv >= KJ - 10, vv)
    print("  J_odd = 0 to the working precision")

    print("\n== C. end-to-end L1 (product-form Riemann sums -> rho0 + 60 c3 J6 + 210 c5 J8)", flush=True)
    e2e = [(40, hE, (6, 9, 12)), (6, [-2, 0, 1, 0, 1, 0], (6, 9, 12)), (20, [-10, 10, 0, 0, 0, 0], (6, 9, 12))]
    if FULL:
        e2e += [(80, [2 * x for x in hE], (6, 10))]
    for (n, h, Ns) in e2e:
        r = RC.get((n, tuple(h))) or lean_rcoef(n, h)
        rho, c3, c5 = rho0_of(r, n), csum(r, n, 3), csum(r, n, 5)
        K = min(KJ, 2 * max(0, -v2(rho), -v2(c3), -v2(c5)) + 14 * n + 300)
        vS, prec = v2_S(rho, c3, c5, Jb, K)
        NJ = Jb[6][1]
        for N in Ns:
            T = riemann_product(n, h, N, K)
            E = max([0] + [-v2(x) for x in (rho, 60 * c3, 210 * c5) if x != 0]) + NJ + N
            S_sc = (to_mod(rho, E, K) + to_mod(60 * c3, E - NJ, K) * Jb[6][0] + to_mod(210 * c5, E - NJ, K) * Jb[8][0]) % (1 << K)
            Rn_sc = (T * pow(2, E - N, 1 << K)) % (1 << K)
            dv = v2mod(Rn_sc - S_sc, E, K)
            vR = v2mod(Rn_sc, E, K)
            print("  n=%d h=%s N=%d: v2(S)=%s  v2(R_N)=%s  v2(R_N - S)=%s  (precision %d)" % (n, h, N, vS, vR, dv, K - E))
            check("L1 end-to-end n=%d N=%d" % (n, N), vS is not None and (dv is None or dv > vS + N - 25), (vS, dv))

    print("\n== D. Stmt_Valuation uniformity: deficit 12n - v2(S) over extreme admissible h", flush=True)
    vcases = []
    for n in (10, 16, 20, 24, 30, 40) + ((60, 80) if FULL else ()):
        hlf = n // 2
        cands = [[0] * 6, [-hlf, hlf, 0, 0, 0, 0], [-hlf, 0, 0, 0, 0, hlf],
                 [-hlf, hlf // 2, hlf - hlf // 2, 0, 0, 0],
                 [-hlf] + [hlf // 5] * 4 + [hlf - 4 * (hlf // 5)],
                 [-1, 1, 0, 0, 0, 0], [-(n // 4), n // 4, 0, 0, 0, 0]]
        if n % 40 == 0:
            cands.append([(n // 40) * x for x in hE])
        for h in cands:
            if admissible(n, h) and (n, h) not in vcases:
                vcases.append((n, h))
    worst = 0
    for (n, h) in vcases:
        r = RC.get((n, tuple(h))) or lean_rcoef(n, h)
        rho, c3, c5 = rho0_of(r, n), csum(r, n, 3), csum(r, n, 5)
        K = min(KJ, 2 * max(0, -v2(rho), -v2(c3), -v2(c5)) + 14 * n + 300)
        vS, prec = v2_S(rho, c3, c5, Jb, K)
        check("S != 0 (n=%d h=%s)" % (n, h), vS is not None, "precision %d" % prec)
        if vS is None:
            continue
        de = 12 * n - vS
        worst = max(worst, de / math.log2(n + 1))
        print("  n=%3d h=%-28s v2(S)=%5d  deficit=%3d  deficit/log2(n+1)=%.2f" % (n, h, vS, de, de / math.log2(n + 1)))
    print("  max deficit/log2(n+1) = %.2f" % worst)
    check("Valuation: deficit <= 8 log2(n+1) on tested cases", worst <= 8, worst)

    print("\n== E. gap statements at finite n along config E (n = 40 m, h = m hE)", flush=True)
    ref = {}
    if VERIF:
        try:
            for line in open(os.path.join(VERIF, "E6.jsonl")):
                d = json.loads(line)
                ref[d["n"]] = d
        except Exception as e:
            print("  (verifier data unavailable: %s)" % e)
    ms = (1, 2, 3) + ((4,) if FULL else ())
    for m in ms:
        n, h = 40 * m, [m * x for x in hE]
        r = RC.get((n, tuple(h))) or lean_rcoef(n, h)
        rho, c3, c5 = rho0_of(r, n), csum(r, n, 3), csum(r, n, 5)
        Z7, Z9 = 46080 * c3, 860160 * c5
        raw = max(lnabs(rho), lnabs(Z7), lnabs(Z9)) / n
        D = 1
        for x in (rho, Z7, Z9):
            D = D * x.denominator // math.gcd(D, x.denominator)
        Do = D >> ((D & -D).bit_length() - 1)
        K = min(KJ, 2 * max(0, -v2(rho), -v2(c3), -v2(c5)) + 14 * n + 300)
        vS, prec = v2_S(rho, c3, c5, Jb, K)
        Dc = 2 ** (6 * n) * math.factorial(n) ** 6 * math.lcm(*range(1, 2 * n + 1)) ** 10
        check("ClearsDen(Dcrude) n=%d" % n, all((Dc * x).denominator == 1 for x in (rho, Z7, Z9)))
        check("growth: raw/n < gE n=%d" % n, raw < -0.72, raw)
        check("denominators: ln(odd D)/n < deltaE n=%d" % n, math.log(Do) / n < 9, math.log(Do) / n)
        check("S != 0 n=%d" % n, vS is not None, "precision %d" % prec)
        if vS is None:
            continue
        check("no prime > n in D n=%d" % n, all(Do % q for q in primes(3 * n) if q > n))
        B = abs(D * rho) + abs(D * Z7) + abs(D * Z9)
        crit = (lnabs(B) - (vS + v2(D)) * LOG2) / n
        sq = [q for q in primes(n) if q * q > n and q > 2]
        ls_ok = [q for q in sq if rho != 0 and (Z7 == 0 or vq(rho, q) < vq(Z7, q)) and (Z9 == 0 or vq(rho, q) < vq(Z9, q))]
        g7 = min(vq(Z7, q) - vq(rho, q) for q in sq); g9 = min(vq(Z9, q) - vq(rho, q) for q in sq)
        vr = [vq(rho, q) for q in sq]
        v7 = min(vq(Z7, q) for q in sq); v9 = min(vq(Z9, q) for q in sq)
        maxe = max(vq(Do, q) for q in sq)
        print("  n=%d: raw/n=%+.6f (rho0 %+.6f, Z7 %+.6f, Z9 %+.6f)  ln(oddD)/n=%.6f  v2S=%s  12n-v2S=%s  crit=%+.4f"
              % (n, raw, lnabs(rho) / n, lnabs(Z7) / n, lnabs(Z9) / n, math.log(Do) / n, vS, 12 * n - vS, crit))
        print("        LS: %d/%d primes in (sqrt n, n] ok; min gaps (Z7,Z9) = (%d,%d); v_q(rho0) in [%d,%d]; min v_q(Z7)=%d min v_q(Z9)=%d; max exp in odd D (q>sqrt n) = %d"
              % (len(ls_ok), len(sq), g7, g9, min(vr), max(vr), v7, v9, maxe))
        check("LaiSprang all q in (sqrt n, n] n=%d" % n, len(ls_ok) == len(sq))
        if n in ref:
            d = ref[n]
            ok = (abs(d["rawparts"]["rho0"] - lnabs(rho) / n) < 1e-9 and abs(d["rawparts"]["z7"] - lnabs(Z7) / n) < 1e-9
                  and abs(d["rawparts"]["z9"] - lnabs(Z9) / n) < 1e-9 and abs(d["lnDodd_n"] - math.log(Do) / n) < 1e-9
                  and d["v2S"] == vS)
            check("fingerprint vs verifier E6.jsonl n=%d" % n, ok, d)
            print("        verifier E6.jsonl fingerprint (|rho0|, |Z7|, |Z9|, odd D, v2S): %s" % ("MATCH" if ok else "MISMATCH"))

    print("\n== F. Lai-Sprang condition at q = n - 1 prime (recommended GAP 3 route)", flush=True)
    for n in ((80, 240, 360) if FULL else (80,)):
        m, q = n // 40, n - 1
        r = RC.get((n, tuple(m * x for x in hE))) or lean_rcoef(n, [m * x for x in hE])
        rho = rho0_of(r, n)
        Z7, Z9 = 46080 * csum(r, n, 3), 860160 * csum(r, n, 5)
        a, b, c = vq(rho, q), vq(Z7, q), vq(Z9, q)
        print("  n=%d q=%d: (v_q rho0, v_q Z7, v_q Z9) = (%d, %d, %d)   [track claim: -9, >= -3, >= -1]" % (n, q, a, b, c))
        check("LS at q=n-1, n=%d" % n, rho != 0 and a == -9 and b >= -3 and c >= -1, (a, b, c))

    print("\nSUMMARY: %d failures, %.0f s" % (len(FAILS), time.time() - t0))
    for f in FAILS[:30]:
        print("   ", f)
    return 1 if FAILS else 0


if __name__ == "__main__":
    sys.exit(main())
