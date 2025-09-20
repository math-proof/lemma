from util import *


@apply
def apply(x_less_than_y, x_less_than_b):
    x, y = x_less_than_y.of(Greater)
    S[x], b = x_less_than_b.of(Greater)
    from sympy import Max
    return Greater(x, Max(y, b))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, b = Symbol(real=True, given=True)
    Eq << apply(x > y, x > b)

    Eq << Algebra.Gt.of.Gt.relax.apply(Eq[-1], b)

    Eq << Algebra.Gt.of.Gt.relax.apply(Eq[-1], y)


if __name__ == '__main__':
    run()
# created on 2019-07-18
del Max
from . import Max
