from util import *


@apply
def apply(self):
    x = self.of(sinh)
    return Equal(self, -S.ImaginaryUnit * sin(x * S.ImaginaryUnit, evaluate=False))


@prove
def prove(Eq):
    from Lemma import Real

    x = Symbol(real=True)
    Eq << apply(sinh(x))

    Eq << Eq[0].this.find(sin).apply(Real.Sin.eq.Mul.Sinh)

    Eq << Eq[-1].this.rhs.find(sinh).apply(Real.Sinh.eq.Neg.Sinh)




if __name__ == '__main__':
    run()
# created on 2023-11-26
