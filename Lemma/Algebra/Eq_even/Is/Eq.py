from util import *


@apply
def apply(self):
    n = self.of(Equal[Expr % 2, 0])
    return Equal((-1) ** n, 1)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
#     n = q * d + r
    n = Symbol(integer=True)

    Eq << apply(Equal(n % 2, 0))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.EqPow.of.Eq_even)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq_even.given.Eq)


if __name__ == '__main__':
    run()
# created on 2019-10-11
