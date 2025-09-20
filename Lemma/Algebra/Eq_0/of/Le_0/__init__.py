from util import *


@apply
def apply(given):
    x = given.of(Expr <= 0)
    assert x >= 0
    return Equal(x, 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(nonnegative=True)
    Eq << apply(x <= 0)

    Eq << GreaterEqual(x, 0, plausible=True)

    Eq << Algebra.Eq.of.Ge.Le.apply(Eq[-1], Eq[0])

    


if __name__ == '__main__':
    run()
# created on 2018-03-15
from . import Ge_0
# updated on 2025-04-12
