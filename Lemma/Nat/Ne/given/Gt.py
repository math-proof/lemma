from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Unequal)
    return Greater(lhs, rhs)


@prove
def prove(Eq):
    x, y = Symbol(real=True, given=True)

    Eq << apply(Unequal(x, y))

    Eq << ~Eq[0]

    Eq <<= Eq[-1] & Eq[1]

    Eq <<= Eq[1] & Eq[-1]


if __name__ == '__main__':
    run()

# created on 2021-09-06
