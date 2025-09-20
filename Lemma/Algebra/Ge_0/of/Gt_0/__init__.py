from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return GreaterEqual(x, 0)


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True, given=True)

    Eq << apply(x > 0)

    Eq << Algebra.Ge.of.Gt.relax.apply(Eq[0])


if __name__ == '__main__':
    run()

# created on 2018-07-16
from . import Ge_0
