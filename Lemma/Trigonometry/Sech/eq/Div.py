from util import *


@apply
def apply(self):
    x = self.of(sech)
    return Equal(self, 2 / (Exp(x) + Exp(-x)), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(sech(x))

    Eq << Eq[0].this.lhs.apply(Trigonometry.Sech.eq.Inv.Cosh)

    Eq << Eq[-1].this.find(cosh).apply(Trigonometry.Cosh.eq.Add.Exp)

    Eq << Eq[-1] / 2


if __name__ == '__main__':
    run()
# created on 2023-11-26
