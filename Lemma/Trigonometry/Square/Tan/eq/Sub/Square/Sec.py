from util import *


@apply
def apply(self):
    x = self.of(tan ** 2)
    return Equal(self, sec(x) ** 2 - 1)


@prove
def prove(Eq):
    from Lemma import Trigonometry, Algebra

    x = Symbol(real=True)
    Eq << apply(tan(x) ** 2)

    Eq << Eq[0].this.find(tan).apply(Trigonometry.Tan.eq.Div)

    Eq << Eq[-1].this.find(sin ** 2).apply(Trigonometry.Square.Sin.eq.Sub.Square.Cos)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(sec).apply(Trigonometry.Sec.eq.Inv.Cos)


if __name__ == '__main__':
    run()
# created on 2023-10-03
