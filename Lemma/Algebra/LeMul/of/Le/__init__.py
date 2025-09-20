from util import *


@apply
def apply(given, factor):
    lhs, rhs = given.of(LessEqual)
    assert factor >= 0

    return LessEqual(lhs * factor, rhs * factor, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True, given=True)
    k = Symbol(real=True, given=True, nonnegative=True)
    Eq << apply(x <= y, k)

    Eq << GreaterEqual(k, 0, plausible=True)

    Eq << Eq[0] - y

    Eq << Algebra.Le_0.of.Ge_0.Le_0.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Algebra.Le.of.Le_0.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-06-17

del Le
from . import Le
