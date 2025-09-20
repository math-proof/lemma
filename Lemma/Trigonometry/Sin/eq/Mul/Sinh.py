from util import *


@apply
def apply(self):
    x = self.of(sin)
    return Equal(self, -S.ImaginaryUnit * sinh(x * S.ImaginaryUnit, evaluate=False))


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(sin(x))

    Eq << Eq[0].this.find(sinh).apply(Trigonometry.Sinh.eq.Sub.Exp)

    Eq << Eq[-1].this.lhs.apply(Trigonometry.Sin.eq.Add.ExpI)


if __name__ == '__main__':
    run()
# created on 2023-11-26
