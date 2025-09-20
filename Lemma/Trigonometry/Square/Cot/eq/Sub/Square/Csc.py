from util import *


@apply
def apply(self):
    x = self.of(Cot ** 2)
    return Equal(self, csc(x) ** 2 - 1)


@prove
def prove(Eq):
    from Lemma import Trigonometry, Algebra

    x = Symbol(real=True)
    Eq << apply(cot(x) ** 2)

    Eq << Eq[0].this.find(cot).apply(Trigonometry.Cot.eq.Div)

    Eq << Eq[-1].this.find(cos ** 2).apply(Trigonometry.Square.Cos.eq.Sub.Square.Sin)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(csc).apply(Trigonometry.Csc.eq.Inv.Sin)


if __name__ == '__main__':
    run()
# created on 2023-10-03
