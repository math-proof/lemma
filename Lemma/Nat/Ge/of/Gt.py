from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Greater)
    return GreaterEqual(lhs, rhs)


@prove
def prove(Eq):
    x, y = Symbol(integer=True, given=True)
    Eq << apply(x > y)

    Eq << ~Eq[-1]

    Eq <<= Eq[0] & Eq[-1]

    


if __name__ == '__main__':
    run()
# created on 2018-06-28
# updated on 2023-04-18
