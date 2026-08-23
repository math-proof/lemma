from util import *


@apply
def apply(given):
    x, y = given.of(Expr - Expr >= 0)
    return LessEqual(y, x)


@prove
def prove(Eq):
    a, b = Symbol(real=True, given=True)

    Eq << apply(LessEqual(0, a - b))

    Eq << Eq[0] + b

    Eq << Eq[-1]


if __name__ == '__main__':
    run()
# created on 2020-05-10

from . import scale
