"""Rational certificates for log and arctan (companion of Landscape/Numerics.lean).

Every bound is exact rational arithmetic (fractions.Fraction); the Lean side re-checks each
side condition with norm_num, so nothing here needs to be trusted.

  log q  : q = 2^k * t, t in [1, 2), z = (t-1)/(t+1) in [0, 1/3);
           Slog(z) <= log t <= Slog(z) + Rlog(z);  log 2 in [C_LO, C_HI] (Real.log_two_gt/lt_d9).
  arctan : u >= 0 reduced to w in [0, 1/2] (R1: w = u; R2: w = (1-u)/(1+u), u in (1/2, 1];
           R3: w = (u-1)/(u+1), u in (1, 2]; R4: w = 1/u, u > 2), Pat8(w) <= arctan w <= Pat9(w).
Bounds are rounded outward to 12 decimals.
"""
from fractions import Fraction as Fr

C_HI = Fr(6931471808, 10**10)
C_LO = Fr(6931471803, 10**10)
DEC = 10**12


def lean_q(q):
    q = Fr(q)
    if q.denominator == 1:
        return "(%d : ℝ)" % q.numerator
    return "(%d / %d : ℝ)" % (q.numerator, q.denominator)


def Slog(z): return 2*(z + z**3/3 + z**5/5 + z**7/7 + z**9/9 + z**11/11)
def Rlog(z): return 2*z**13/(13*(1 - z**2))


def ceil_dec(x):
    return Fr(-((-x.numerator*DEC) // x.denominator), DEC)


def floor_dec(x):
    return Fr((x.numerator*DEC) // x.denominator, DEC)


def red_pow2(q):
    k = 0
    t = Fr(q)
    while t >= 2:
        t /= 2; k += 1
    while t < 1:
        t *= 2; k -= 1
    return k, t


def log_upper(q):
    """(U, lean term of type Real.log q <= U)"""
    q = Fr(q); assert q > 0
    k, t = red_pow2(q)
    z = (t - 1)/(t + 1)
    assert 0 <= z < Fr(1, 3)
    if k >= 0:
        U = ceil_dec(Slog(z) + Rlog(z) + k*C_HI)
        assert q <= 2**k * ((1+z)/(1-z))
        term = ("(log_le_of_le_mul (q := %s) (z := %s) (U := %s) %d (by norm_num) (by norm_num) "
                "(by norm_num) (by norm_num) (by norm_num [Slog, Rlog]))") % (lean_q(q), lean_q(z), lean_q(U), k)
    else:
        U = ceil_dec(Slog(z) + Rlog(z) - (-k)*C_LO)
        assert q * 2**(-k) <= (1+z)/(1-z)
        term = ("(log_le_of_mul_le (q := %s) (z := %s) (U := %s) %d (by norm_num) (by norm_num) "
                "(by norm_num) (by norm_num) (by norm_num [Slog, Rlog]))") % (lean_q(q), lean_q(z), lean_q(U), -k)
    return U, term


def log_lower(q):
    """(L, lean term of type L <= Real.log q)"""
    q = Fr(q); assert q > 0
    k, t = red_pow2(q)
    z = (t - 1)/(t + 1)
    if k >= 0:
        L = floor_dec(Slog(z) + k*C_LO)
        term = ("(le_log_of_mul_le (q := %s) (z := %s) (L := %s) %d (by norm_num) (by norm_num) "
                "(by norm_num) (by norm_num [Slog]))") % (lean_q(q), lean_q(z), lean_q(L), k)
    else:
        L = floor_dec(Slog(z) - (-k)*C_HI)
        term = ("(le_log_of_le_mul (q := %s) (z := %s) (L := %s) %d (by norm_num) (by norm_num) "
                "(by norm_num) (by norm_num) (by norm_num [Slog]))") % (lean_q(q), lean_q(z), lean_q(L), -k)
    return L, term


def Pat8(w): return w - w**3/3 + w**5/5 - w**7/7 + w**9/9 - w**11/11 + w**13/13 - w**15/15
def Pat9(w): return Pat8(w) + w**17/17


def atan_upper(u):
    """u >= 0: (alpha, c, lean term) with arctan u <= alpha*pi + c (term states it in wrapper form)"""
    u = Fr(u); assert u >= 0
    if u <= Fr(1, 2):
        U = ceil_dec(Pat9(u))
        return Fr(0), U, "(arctan_le_R1 (u := %s) (U := %s) (by norm_num) (by norm_num [Pat9, Pat8]))" % (lean_q(u), lean_q(U))
    if u <= 1:
        w = (1 - u)/(1 + u)
        L = floor_dec(Pat8(w))
        return Fr(1, 4), -L, ("(arctan_le_R2 (u := %s) (w := %s) (L := %s) (by norm_num) (by norm_num) "
                              "(by norm_num) (by norm_num [Pat8]))") % (lean_q(u), lean_q(w), lean_q(L))
    if u <= 2:
        w = (u - 1)/(u + 1)
        U = ceil_dec(Pat9(w))
        return Fr(1, 4), U, ("(arctan_le_R3 (u := %s) (w := %s) (U := %s) (by norm_num) (by norm_num) "
                             "(by norm_num) (by norm_num [Pat9, Pat8]))") % (lean_q(u), lean_q(w), lean_q(U))
    w = 1/u
    L = floor_dec(Pat8(w))
    return Fr(1, 2), -L, ("(arctan_le_R4 (u := %s) (w := %s) (L := %s) (by norm_num) (by norm_num) "
                          "(by norm_num [Pat8]))") % (lean_q(u), lean_q(w), lean_q(L))


def atan_lower(u):
    """u >= 0: (alpha, c, lean term) with alpha*pi + c <= arctan u"""
    u = Fr(u); assert u >= 0
    if u <= Fr(1, 2):
        L = floor_dec(Pat8(u))
        return Fr(0), L, "(arctan_ge_R1 (u := %s) (L := %s) (by norm_num) (by norm_num [Pat8]))" % (lean_q(u), lean_q(L))
    if u <= 1:
        w = (1 - u)/(1 + u)
        U = ceil_dec(Pat9(w))
        return Fr(1, 4), -U, ("(arctan_ge_R2 (u := %s) (w := %s) (U := %s) (by norm_num) (by norm_num) "
                              "(by norm_num) (by norm_num [Pat9, Pat8]))") % (lean_q(u), lean_q(w), lean_q(U))
    if u <= 2:
        w = (u - 1)/(u + 1)
        L = floor_dec(Pat8(w))
        return Fr(1, 4), L, ("(arctan_ge_R3 (u := %s) (w := %s) (L := %s) (by norm_num) (by norm_num) "
                             "(by norm_num) (by norm_num [Pat8]))") % (lean_q(u), lean_q(w), lean_q(L))
    w = 1/u
    U = ceil_dec(Pat9(w))
    return Fr(1, 2), -U, ("(arctan_ge_R4 (u := %s) (w := %s) (U := %s) (by norm_num) (by norm_num) "
                          "(by norm_num [Pat9, Pat8]))") % (lean_q(u), lean_q(w), lean_q(U))
