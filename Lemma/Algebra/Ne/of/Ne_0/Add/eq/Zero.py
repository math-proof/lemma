from util import *


def cubic_delta(y, alpha, beta, gamma):
    return y ** 3 - alpha * y ** 2 / 2 - gamma * y - beta ** 2 / 8 + alpha * gamma / 2


@apply
def apply(is_nonzero, fy, y):
    beta = is_nonzero.of(Unequal[0])

    from Lemma.Algebra.And_Imp_Or_EqS.of.Add.eq.Zero.cubic import cubic_coefficient
    S[1], a, b, c = cubic_coefficient(fy, y)

    alpha = -2 * a
    gamma = -b

    assert c == -beta ** 2 / 8 + alpha * gamma / 2

    return Unequal(y, alpha / 2)


@prove
def prove(Eq):
    from Lemma import Algebra

    y, alpha, beta, gamma = Symbol(complex=True, given=True)
    fy = cubic_delta(y, alpha, beta, gamma)
    Eq << apply(Unequal(beta, 0), Equal(fy, 0), y=y)

    Eq << ~Eq[-1]

    Eq << Eq[1].subs(Eq[-1]) * -8

    Eq << Algebra.Eq_0.of.Square.eq.Zero.complex.apply(Eq[-1])

    Eq << ~Eq[-1]

    # https://planetmath.org/QuarticFormula
    # https://en.wikipedia.org/wiki/Quartic_equation


if __name__ == '__main__':
    run()
# created on 2018-11-11
