from util import *


@apply
def apply(given, factor):
    lhs, rhs = given.of(Less)

    assert factor >= 0

    return LessEqual(lhs * factor, rhs * factor)


@prove
def prove(Eq):
    from Lemma import Algebra, Int, Int
    x, y = Symbol(real=True, given=True)
    k = Symbol(real=True, given=True, nonnegative=True)

    Eq << apply(Less(x, y), k)

    Eq << GreaterEqual(k, 0, plausible=True)

    Eq << Eq[0] - y

    Eq << Int.Le_0.of.Ge_0.Lt_0.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Algebra.Le.of.Le_0.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-11-24
del Le
from . import Le
