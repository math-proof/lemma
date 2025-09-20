from util import *


@apply
def apply(self):
    arg = self.of(Abs)
    return Equal(self, Abs(~arg, evaluate=False))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(complex=True)
    Eq << apply(Abs(x + ~y))

    Eq << Eq[0].this.lhs.apply(Algebra.Abs.eq.Sqrt)

    Eq << Eq[-1].this.rhs.apply(Algebra.Abs.eq.Sqrt)

    Eq << Eq[-1].this.rhs.find((Expr - Expr) ** 2).apply(Algebra.Square.Neg)




if __name__ == '__main__':
    run()
# created on 2023-06-24
