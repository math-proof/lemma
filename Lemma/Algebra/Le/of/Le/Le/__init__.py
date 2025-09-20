from util import *


@apply
def apply(a_less_than_x, x_less_than_b):
    a, x = a_less_than_x.of(LessEqual)
    _x, b = x_less_than_b.of(LessEqual)
    if x != _x:
        a, x, S[x], b = _x, b, a, x
    return LessEqual(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, x, b = Symbol(real=True)
    Eq << apply(a <= x, x <= b)

    Eq << Eq[0] + Eq[1]

    Eq << Eq[-1].this.apply(Algebra.LeAddS.Is.Le)


if __name__ == '__main__':
    run()
# created on 2018-02-26

from . import quadratic
from . import subst
