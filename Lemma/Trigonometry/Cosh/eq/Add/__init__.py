from util import *


@apply
def apply(self, index=-1):
    x, y = std.array_split(self.of(cosh[Add]), index)
    x, y = Add(*x), Add(*y)
    return Equal(self, Cosh(x) * Cosh(y) + sinh(x) * sinh(y))


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x, y = Symbol(real=True)
    Eq << apply(cosh(x + y))

    Eq << Eq[0].this.lhs.apply(Trigonometry.Cosh.eq.Add.Exp)

    Eq << Eq[-1].this.rhs.find(Cosh).apply(Trigonometry.Cosh.eq.Add.Exp)

    Eq << Eq[-1].this.rhs.find(Cosh).apply(Trigonometry.Cosh.eq.Add.Exp)

    Eq << Eq[-1].this.rhs.find(Sinh).apply(Trigonometry.Sinh.eq.Sub.Exp)

    Eq << Eq[-1].this.rhs.find(Sinh).apply(Trigonometry.Sinh.eq.Sub.Exp)

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1].this.lhs.expand()

    # https://baike.baidu.com/item/%E5%92%8C%E8%A7%92%E5%85%AC%E5%BC%8F



if __name__ == '__main__':
    run()
# created on 2023-11-26

del Exp
from . import Exp
