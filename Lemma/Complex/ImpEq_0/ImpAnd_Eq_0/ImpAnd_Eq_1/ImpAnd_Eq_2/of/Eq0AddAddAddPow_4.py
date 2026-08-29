from util import *


@apply
def apply(fx, x=None):
    from Lemma.Complex.ImpEq_0.ImpAnd_Eq_0.ImpAnd_Eq_1.ImpAnd_Eq_2.of.Eq0AddAddAddAddPow_4 import quartic_coefficient
    from Lemma.Complex.Eq0AddAddAddPow_3.given.Eq_Ite_SubAdd_Pow_Inv3.EqSubCeilSSubDivMul3Arg import cubic_solve
    from Lemma.Rat.Ne_Div_2.of.Eq0AddSubSub_Pow_3.Ne_0 import cubic_delta
    fx = fx.of(Equal[0])
    S[1], S[0], alpha, beta, gamma = quartic_coefficient(fx, x=x)

    w = -S.One / 2 + sqrt(3) * S.ImaginaryUnit / 2

    y_delta = cubic_delta(x, alpha, beta, gamma)
    _d, Y0, Y1, Y2 = cubic_solve(y_delta, x)

    delta = -(alpha ** 2 / 3 + 4 * gamma) ** 3 / 27 + (-alpha ** 3 / 27 + 4 * alpha * gamma / 3 - beta ** 2 / 2) ** 2

    V = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 - sqrt(delta)
    U = alpha ** 3 / 27 - 4 * alpha * gamma / 3 + beta ** 2 / 2 + sqrt(delta)

    A = U ** (S.One / 3)
    B = V ** (S.One / 3)

    from Lemma.Complex.OrOrSEqS_Div_2.of.Eq0Add_Pow_4.Ne_0.ferrari import solver_set
    delta = alpha ** 2 - 4 * gamma

    return Imply(Equal(beta, 0), Equal(x, sqrt(sqrt(delta) / 2 - alpha / 2)) | Equal(x, -sqrt(sqrt(delta) / 2 - alpha / 2)) | Equal(x, sqrt(-sqrt(delta) / 2 - alpha / 2)) | Equal(x, -sqrt(-sqrt(delta) / 2 - alpha / 2))), \
        Imply(Unequal(beta, 0) & Equal(_d, 0), solver_set(0, A, B, x, alpha, beta, w)), \
        Imply(Unequal(beta, 0) & Equal(_d % 3, 1), solver_set(1, A, B, x, alpha, beta, w)), \
        Imply(Unequal(beta, 0) & Equal(_d % 3, 2), solver_set(2, A, B, x, alpha, beta, w))


@prove
def prove(Eq):
    from Lemma import Bool, Complex

    x, alpha, beta, gamma = Symbol(complex=True, given=True)
    fx = x ** 4 + alpha * x ** 2 + beta * x + gamma
    Eq << apply(Equal(fx, 0), x=x)

    Eq << Bool.Imp.ImpNot.of.Cond.apply(Eq[0], cond=Equal(beta, 0))

    Eq <<= Bool.ImpEq.of.ImpEq.subst.apply(Eq[-2]), Bool.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-2].this.rhs.apply(Complex.OrOrSEqS.of.Eq0AddAddPow_4.biquadratic, x)

    Eq << Bool.Imp.Imp.of.Imp_And.apply(Eq[-1].this.rhs.apply(Complex.OrOrSEqS_Div_2.of.Eq0Add_Pow_4.Ne_0.ferrari, x), None)


if __name__ == '__main__':
    run()

# created on 2018-11-27
