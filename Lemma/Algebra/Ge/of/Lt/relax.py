from util import *


@apply
def apply(given):
    x, y = given.of(Less)

    return GreaterEqual(y, x)


@prove
def prove(Eq):
    x, y = Symbol(integer=True, given=True)
    Eq << apply(x < y)

    Eq << ~Eq[-1]

    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    run()
# created on 2021-09-15
