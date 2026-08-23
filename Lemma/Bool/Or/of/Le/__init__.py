from util import *


@apply
def apply(given):
    lhs, rhs = given.of(LessEqual)
    return Or(Less(lhs, rhs), Equal(lhs, rhs))


@prove
def prove(Eq):
    x, y = Symbol(real=True, given=True)
    Eq << apply(x <= y)

    Eq << ~Eq[-1]

    Eq << Eq[-1].simplify()

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2021-08-10

from . import split
