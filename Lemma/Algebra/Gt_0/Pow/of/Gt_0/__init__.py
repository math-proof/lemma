from util import *


@apply
def apply(given, n):
    x = given.of(Expr > 0)
    return Greater(x ** n, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(x > 0, n)

    Eq.gt_zero, Eq.le_zero = Bool.Cond.given.Imp.ImpNot.apply(Eq[1], cond=n > 0)

    Eq << Bool.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq.gt_zero)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.Pow.of.Gt_0.Gt_0)

    Eq << Bool.Imp.given.And.Imp.split.apply(Eq.le_zero, cond=n < 0)

    Eq << Bool.Imp.given.ImpEq.apply(Eq[-1])

    Eq << Bool.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq[-2])


    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.Pow.of.Lt_0.Gt_0)


if __name__ == '__main__':
    run()
# created on 2018-08-22
# updated on 2023-04-15
from . import Gt_0
