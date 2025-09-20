from util import *


@apply
def apply(given):
    x, y = given.of(Less)
    assert y <= 0
    return Less(x, 0)


@prove
def prove(Eq):
    x = Symbol(real=True, given=True)
    y = Symbol(real=True, given=True, positive=False)
    Eq << apply(x < y)

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2020-05-14
