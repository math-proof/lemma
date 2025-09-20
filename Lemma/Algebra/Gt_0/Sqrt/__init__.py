from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return sqrt(x) > 0


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(real=True)
    Eq << apply(x > 0)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Gt_0.Sqrt.of.Gt_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.given.Gt_0.Sqrt)


if __name__ == '__main__':
    run()
# created on 2023-06-20
from . import of
