from util import *


@apply
def apply(given):
    xy = given.of(Unequal[0])
    x, y = xy.of(Expr - Expr)

    return Unequal(x, y)


@prove
def prove(Eq):
    a, b = Symbol(real=True, given=True)

    Eq << apply(Unequal(0, a - b))

    Eq << Eq[0] + b

    Eq << Eq[-1].reversed



if __name__ == '__main__':
    run()
# created on 2021-09-19

del Ne
from . import Ne
del Add
from . import Add
