from util import *


@apply
def apply(sinx):
    i = S.ImaginaryUnit
    x = sinx.of(Sin)
    return Equal(sinx, (E ** (i * x) - E ** (-i * x)) / (2 * i))


@prove
def prove(Eq):
    from Lemma import Calculus, Trigonometry

    x = Symbol(real=True)
    Eq << apply(sin(x))

    Eq << Eq[0].find(Exp).this.apply(Trigonometry.ExpMulI.eq.AddCos_MulISin.Euler)

    Eq << Eq[0].find(- ~Exp).this.apply(Trigonometry.ExpMulI.eq.AddCos_MulISin.Euler)

    Eq << Eq[-2] - Eq[-1]

    Eq << Eq[-1] / (2 * S.ImaginaryUnit)

    Eq << Eq[-1].reversed

    Eq << Eq[0].this.rhs.expand()


if __name__ == '__main__':
    run()

# created on 2018-06-15
