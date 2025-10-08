from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 0])
    return Equal(n // 2, n / 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    # n = q * d + r
    n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 0))

    Eq << Algebra.Any.of.Eq_even.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(Algebra.EqDiv.of.Eq, 2, simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.EqFloor.of.Eq, ret=0)

    Eq << Eq[-1].this.expr.apply(Bool.Eq.of.Eq.Eq)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-10-10
