from util import *


@apply
def apply(le, ge):
    a, x = le.of(LessEqual)
    b, _x = ge.of(GreaterEqual)
    if x != _x:
        x, a, S[x], b = b, _x, a, x
    return LessEqual(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra

    a, x, b = Symbol(real=True)
    Eq << apply(a <= x, b >= x)

    Eq << Eq[1].reversed

    Eq << Algebra.Le.of.Le.Le.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-09-10

from . import quadratic
