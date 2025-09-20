from util import *


@apply
def apply(self):
    x = self.of(cosh)
    return Equal(self, cos(x * S.ImaginaryUnit, evaluate=False))


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(cosh(x))

    Eq << Eq[0].this.rhs.apply(Trigonometry.Cos.eq.Cosh)

    Eq << Eq[-1].this.rhs.apply(Trigonometry.Cosh.Neg)




if __name__ == '__main__':
    run()
# created on 2023-11-26
