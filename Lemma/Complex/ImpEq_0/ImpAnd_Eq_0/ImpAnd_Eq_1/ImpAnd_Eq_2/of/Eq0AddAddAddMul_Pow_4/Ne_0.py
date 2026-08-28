from util import *


def solver_set(d, A, B, x, alpha, beta, w, offset=0):
    if d == 0:
        y = A + B
    elif d % 3 == 1:
        y = A * w + B
    elif d % 3 == 2:
        y = A * ~w + B
    else:
        ...

    y0 = -2 * alpha / 3 + y
    y1 = 4 * alpha / 3 + y

    x0 = sqrt(2 * beta / sqrt(y0) - y1) / 2 - sqrt(y0) / 2 + offset
    x1 = -sqrt(2 * beta / sqrt(y0) - y1) / 2 - sqrt(y0) / 2 + offset
    x2 = sqrt(-2 * beta / sqrt(y0) - y1) / 2 + sqrt(y0) / 2 + offset
    x3 = -sqrt(-2 * beta / sqrt(y0) - y1) / 2 + sqrt(y0) / 2 + offset

    return Equal(x, x0) | Equal(x, x1) | Equal(x, x2) | Equal(x, x3)


@apply
def apply(fx, is_nonzero, x=None):
    from Lemma.Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddPow_4 import quartic_coefficient
    from Lemma.Complex.Eq0AddAddAddPow_3.given.Eq_Ite_SubAdd_Pow_Inv3.EqSubCeil_Ite import cubic_solve
    from Lemma.Rat.Ne_Div_2.of.Eq0AddSubSub_Pow_3.Ne_0 import cubic_delta
    fx = fx.of(Equal[0])
    S[1], S[0], alpha, beta, gamma = quartic_coefficient(fx, x=x)

    w = -S.One / 2 + sqrt(3) * S.ImaginaryUnit / 2

    y_delta = cubic_delta(x, alpha, beta, gamma)
    _d, Y0, Y1, Y2 = cubic_solve(y_delta, x)

    S[beta] = is_nonzero.of(Unequal[0])

    delta = -(alpha ** 2 / 3 + 4 * gamma) ** 3 / 27 + (-alpha ** 3 / 27 + 4 * alpha * gamma / 3 - beta ** 2 / 2) ** 2

    V = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 - sqrt(delta)
    U = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 + sqrt(delta)

    A = U ** (S.One / 3)
    B = V ** (S.One / 3)

    return Imply(Equal(_d, 0), solver_set(0, A, B, x, alpha, beta, w)), Imply(Equal(_d % 3, 1), solver_set(1, A, B, x, alpha, beta, w)), Imply(Equal(_d % 3, 2), solver_set(2, A, B, x, alpha, beta, w))


@prove
def prove(Eq):
    from Lemma import Bool, Complex

    x, alpha, beta, gamma = Symbol(complex=True, given=True)
    fx = x ** 4 + alpha * x ** 2 + beta * x + gamma
    Eq << apply(Equal(fx, 0), Unequal(beta, 0), x=x)

    Eq << Bool.Imp.of.Cond.apply(Eq[0] & Eq[1], cond=Eq[2].lhs)

    Eq << Bool.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Complex.OrEqS.of.Eq0AddAddAddPow_4.EqSubCeil_Ite.Ne_0, x)

    Eq << Bool.Imp.of.Cond.apply(Eq[0] & Eq[1], cond=Eq[3].lhs)

    Eq << Bool.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Complex.OrEqS.of.Eq0AddAddAddPow_4.EqModSubCeil_Ite.Ne_0, x)

    Eq << Bool.Imp.of.Cond.apply(Eq[0] & Eq[1], cond=Eq[4].lhs)

    Eq << Bool.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Complex.OrEqS.of.Eq0AddAddAddPow_4.EqModSubCeil_Ite.Ne_0, x)

    # https://planetmath.org/QuarticFormula
    # https://en.wikipedia.org/wiki/Quartic_equation


if __name__ == '__main__':
    run()
# created on 2018-11-27
