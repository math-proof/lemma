from util import *


@apply
def apply(given, factor):
    lhs, rhs = given.of(Greater)

    assert factor > 0

    return Greater(lhs * factor, rhs * factor)


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y = Symbol(real=True, given=True)
    k = Symbol(real=True, given=True, positive=True)

    Eq << apply(Greater(x, y), k)

    Eq << Greater(k, 0, plausible=True)

    Eq << Eq[0] - y

    Eq << Algebra.Gt_0.of.Gt_0.Gt_0.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Algebra.Gt.of.Sub.gt.Zero.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-07-23

del Gt
from . import Gt
