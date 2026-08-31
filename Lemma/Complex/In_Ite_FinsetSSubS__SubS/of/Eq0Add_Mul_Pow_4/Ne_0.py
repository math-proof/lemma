from util import *


def quartic_coefficient(fx, x):
    fx = fx.as_poly(x)
    if fx.degree() != 4:
        return
    a = fx.nth(4)
    b = fx.nth(3)
    c = fx.nth(2)
    d = fx.nth(1)
    e = fx.nth(0)
    return a, b, c, d, e


@apply
def apply(is_nonzero, given, x=None):
    _a = is_nonzero.of(Unequal[0])
    fx, rhs = given.of(Equal)
    if not rhs.is_Zero:
        fx -= rhs

    S[_a], _b, _c, _d, _e = quartic_coefficient(fx, x=x)
    a, b, c, d = _b / _a, _c / _a, _d / _a, _e / _a

    alpha = b - 3 * a ** 2 / 8
    beta = a ** 3 / 8 + c - a * b / 2
    gamma = a ** 2 * b / 16 + d - 3 * a ** 4 / 256 - a * c / 4

    w = -S.One / 2 + sqrt(3) * S.ImaginaryUnit / 2
    from Lemma.Rat.Ne_Div_2.of.Eq0AddSubSub_Pow_3.Ne_0 import cubic_delta
    from Lemma.Complex.Eq0Add_Pow_3.given.Eq_SubAdd_Pow_SubCeilSSubDivMul3Arg.sub import cubic_solve
    y_delta = cubic_delta(x, alpha, beta, gamma)
    D, Y0, Y1, Y2 = cubic_solve(y_delta, x)
    D = Symbol(D)

    delta = -(alpha ** 2 / 3 + 4 * gamma) ** 3 / 27 + (-alpha ** 3 / 27 + 4 * alpha * gamma / 3 - beta ** 2 / 2) ** 2

    V = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 - sqrt(delta)
    U = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 + sqrt(delta)

    A = U ** (S.One / 3)
    B = V ** (S.One / 3)

    from Lemma.Complex.In_FinsetDivS_2DivS_2.of.Eq0Add_Pow_4.Ne_0 import solver_set
    delta = alpha ** 2 - 4 * gamma

    A = Symbol(A)
    B = Symbol(B)
    return Imply(Equal(beta, 0), Equal(x, sqrt((sqrt(delta) - alpha) / 2) - a / 4) | Equal(x, -sqrt((sqrt(delta) - alpha) / 2) - a / 4) | Equal(x, sqrt((-sqrt(delta) - alpha) / 2) - a / 4) | Equal(x, -sqrt((-sqrt(delta) - alpha) / 2) - a / 4)), \
            Imply(Unequal(beta, 0) & Equal(D, 0), solver_set(0, A, B, x, alpha, beta, w, -a / 4)), \
            Imply(Unequal(beta, 0) & Equal(D % 3, 1), solver_set(1, A, B, x, alpha, beta, w, -a / 4)), \
            Imply(Unequal(beta, 0) & Equal(D % 3, 2), solver_set(2, A, B, x, alpha, beta, w, -a / 4))


@prove(slow=True)
def prove(Eq):
    from Lemma import Nat, Complex

    x, a, b, c, d, e = Symbol(complex=True, given=True)
    Eq << apply(Unequal(a, 0), Equal(a * x ** 4 + b * x ** 3 + c * x ** 2 + d * x + e, 0), x=x)

    Eq << Nat.Div.of.Eq.nonzero.apply(Eq[0], Eq[1])

    Eq << Complex.In_Ite_FinsetSSubS__SubS.of.Eq0Add_Pow_4.apply(Eq[-1], x=x)

    Eq <<= Eq[-4].subs(Eq[2].reversed, Eq[3].reversed, Eq[4].reversed), Eq[-3].subs(Eq[2].reversed, Eq[3].reversed, Eq[4].reversed), Eq[-2].subs(Eq[2].reversed, Eq[3].reversed, Eq[4].reversed), Eq[-1].subs(Eq[2].reversed, Eq[3].reversed, Eq[4].reversed)


if __name__ == '__main__':
    run()

# created on 2018-11-29
