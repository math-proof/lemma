from util import *


@apply
def apply(given):
    x, y = given.of(Less)
    assert x >= 0
    return Greater(y, 0)


@prove
def prove(Eq):
    x = Symbol(real=True, given=True, negative=False)
    y = Symbol(real=True, given=True)
    Eq << apply(x < y)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2019-12-28
