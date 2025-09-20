from util import *


@apply
def apply(self):
    x, y = self.of(Expr + ImaginaryUnit * Expr)
    if x.is_Cos:
        theta = x.of(Cos)
        if y == sin(theta):
            rhs = exp(S.ImaginaryUnit * theta)
        elif y == -sin(theta):
            rhs = exp(-S.ImaginaryUnit * theta)
    return Equal(self, rhs, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(cos(x) - S.ImaginaryUnit * sin(x))

    Eq << Eq[0].this.rhs.apply(Trigonometry.ExpMulI.eq.AddCos_MulISin.Euler)


if __name__ == '__main__':
    run()
# created on 2022-01-20
