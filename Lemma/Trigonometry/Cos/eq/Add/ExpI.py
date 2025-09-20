from util import *


@apply
def apply(cosx):
    i = S.ImaginaryUnit
    x = cosx.of(Cos)
    return Equal(cosx, (E ** (i * x) + E ** (-i * x)) / 2)


@prove
def prove(Eq):
    from Lemma import Calculus, Trigonometry
    x = Symbol(real=True)
    Eq << apply(cos(x))

    Eq << Eq[0].find(Exp).this.apply(Trigonometry.ExpMulI.eq.AddCos_MulISin.Euler)

    Eq << Eq[0].rhs.args[1].args[1].this.apply(Trigonometry.ExpMulI.eq.AddCos_MulISin.Euler)

    Eq << Eq[-2] + Eq[-1]

    Eq << Eq[-1] / 2

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2018-06-14
