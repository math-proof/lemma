from util import *


@apply
def apply(le):
    abs_x, a = le.of(LessEqual)
    x = abs_x.of(Abs)
    return LessEqual(x, a), GreaterEqual(x, -a)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(abs(x) <= a)

    Eq << Algebra.LeAbs.of.Le.Le.apply(Eq[1], -Eq[2])






if __name__ == '__main__':
    run()
# created on 2022-01-07

from . import split
