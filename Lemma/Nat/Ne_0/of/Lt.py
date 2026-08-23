from util import *


@apply
def apply(given):
    x, y = given.of(Less)
    assert x >= 0

    return Unequal(y, 0)


@prove
def prove(Eq):
    x = Symbol(real=True, nonnegative=True, given=True)
    y = Symbol(real=True, given=True)
    Eq << apply(x < y)

    Eq << ~Eq[-1]

    Eq <<= Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-09-18
