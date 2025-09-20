from util import *


@apply
def apply(self):
    x = self.of(sech ** 2)
    return Equal(self, 1 - tanh(x) ** 2)


@prove
def prove(Eq):
    from Lemma import Trigonometry, Algebra

    x = Symbol(real=True)
    Eq << apply(sech(x) ** 2)

    Eq << Eq[0].this.find(tanh).apply(Trigonometry.Tanh.eq.Div)

    Eq << Eq[-1].this.find(sinh ** 2).apply(Trigonometry.Square.Sinh.eq.Sub.Square.Cosh)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(cosh).apply(Trigonometry.Cosh.eq.Inv.Sech)


if __name__ == '__main__':
    run()
# created on 2023-11-26
