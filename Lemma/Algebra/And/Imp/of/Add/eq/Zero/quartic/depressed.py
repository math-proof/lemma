from util import *


@apply
def apply(fx, x=None):
    from Lemma.Algebra.And.Imp.of.Add.eq.Zero.quartic.one_leaded import quartic_coefficient
    from Lemma.Algebra.Add.eq.Zero.given.And.Eq.cubic.one_leaded import cubic_solve
    from Lemma.Algebra.Ne.of.Ne_0.Add.eq.Zero import cubic_delta
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

    from Lemma.Algebra.And.Imp.of.Add.eq.Zero.Ne_0.quartic.depressed import solver_set
    delta = alpha ** 2 - 4 * gamma

    return Imply(Equal(beta, 0), Equal(x, sqrt(sqrt(delta) / 2 - alpha / 2)) | Equal(x, -sqrt(sqrt(delta) / 2 - alpha / 2)) | Equal(x, sqrt(-sqrt(delta) / 2 - alpha / 2)) | Equal(x, -sqrt(-sqrt(delta) / 2 - alpha / 2))), \
        Imply(Unequal(beta, 0) & Equal(_d, 0), solver_set(0, A, B, x, alpha, beta, w)), \
        Imply(Unequal(beta, 0) & Equal(_d % 3, 1), solver_set(1, A, B, x, alpha, beta, w)), \
        Imply(Unequal(beta, 0) & Equal(_d % 3, 2), solver_set(2, A, B, x, alpha, beta, w))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, alpha, beta, gamma = Symbol(complex=True, given=True)
    fx = x ** 4 + alpha * x ** 2 + beta * x + gamma
    Eq << apply(Equal(fx, 0), x=x)

    Eq << Bool.And.Imp.of.Cond.split.apply(Eq[0], cond=Equal(beta, 0))

    Eq <<= Bool.ImpEq.of.ImpEq.subst.apply(Eq[-2]), Bool.Imp_And.of.ImpAnd.apply(Eq[-1])

    Eq << Eq[-2].this.rhs.apply(Algebra.Or_Eq.of.Add.eq.Zero.biquadratic, x)

    Eq << Bool.And.Imp.of.Imp.apply(Eq[-1].this.rhs.apply(Algebra.And.Imp.of.Add.eq.Zero.Ne_0.quartic.depressed, x), None)


if __name__ == '__main__':
    run()

# created on 2018-11-27
