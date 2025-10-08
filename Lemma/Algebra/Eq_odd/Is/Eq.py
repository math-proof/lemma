from util import *



@apply
def apply(self):
    n = self.of(Equal[Expr % 2, 1])
    return Equal((-1) ** n, -1)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool
#     n = q * d + r
    n = Symbol(integer=True)

    Eq << apply(Equal(n % 2, 1))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.EqPow.of.Eq_odd)

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq_odd.given.Eq)


if __name__ == '__main__':
    run()
# created on 2019-10-13
