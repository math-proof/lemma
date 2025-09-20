from util import *


@apply
def apply(self):
    x = self.of(cos)
    return Equal(self, cosh(x * S.ImaginaryUnit, evaluate=False))


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(cos(x))

    Eq << Eq[-1].this.rhs.apply(Trigonometry.Cosh.eq.Add.Exp)

    Eq << Eq[-1].this.lhs.apply(Trigonometry.Cos.eq.Add.ExpI)


if __name__ == '__main__':
    run()
# created on 2023-11-26
