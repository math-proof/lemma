from util import *


@apply
def apply(given, m):
    lhs, rhs = given.of(LessEqual)
    return LessEqual(Min(lhs, m), Min(rhs, m))


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y, z = Symbol(real=True, given=True)

    Eq << apply(x <= y, z)

    Eq << Eq[0].reversed

    Eq << Algebra.GeMin.of.Ge.apply(Eq[-1], z)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-11-01
del Le
from . import Le
