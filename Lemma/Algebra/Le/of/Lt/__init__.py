from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Less)
    return LessEqual(lhs, rhs)


@prove
def prove(Eq):
    x, y = Symbol(integer=True, given=True)
    Eq << apply(x < y)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]




if __name__ == '__main__':
    run()
# created on 2018-12-29
# updated on 2023-04-18

from . import strengthen
