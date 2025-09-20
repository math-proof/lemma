from util import *


@apply(simplify=False)
def apply(given, x):
    lhs, rhs = given.of(LessEqual)
    return LessEqual(lhs + x, rhs + x, evaluate=False)


@prove
def prove(Eq):
    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x <= y, z)

    Eq << Eq[0] + z


if __name__ == '__main__':
    run()
# created on 2018-07-04

del Le
del Eq
from . import Eq
from . import Le
