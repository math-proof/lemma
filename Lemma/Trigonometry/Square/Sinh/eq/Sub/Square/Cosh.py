from util import *


@apply
def apply(self):
    x = self.of(Sinh ** 2)
    return Equal(self, cosh(x) ** 2 - 1)


@prove
def prove(Eq):
    from Lemma import Trigonometry, Algebra

    x = Symbol(real=True)
    Eq << apply(sinh(x) ** 2)

    Eq << Eq[-1].this.find(sinh).apply(Trigonometry.Sinh.eq.Sub.Exp)

    Eq << Eq[-1].this.lhs.apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)

    Eq << Eq[-1].this.find(cosh).apply(Trigonometry.Cosh.eq.Add.Exp)

    Eq << Eq[-1].this.find(Add ** 2).apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)


if __name__ == '__main__':
    run()
# created on 2023-11-26
