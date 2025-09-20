from util import *


@apply
def apply(self):
    x = self.of(csch)
    return Equal(self, 2 / (Exp(x) - Exp(-x)), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(csch(x))

    Eq << Eq[0].this.lhs.apply(Trigonometry.Csch.eq.Inv.Sinh)

    Eq << Eq[-1].this.find(sinh).apply(Trigonometry.Sinh.eq.Sub.Exp)

    Eq << Eq[-1] / 2




if __name__ == '__main__':
    run()
# created on 2023-11-26
