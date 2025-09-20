from util import *


@apply
def apply(given):
    x, y = given.of(Equal)
    return x <= y, x >= y


@prove
def prove(Eq):
    x, y = Symbol(real=True)
    Eq << apply(Equal(x, y))
    Eq <<= Eq[1] & Eq[2]


if __name__ == '__main__':
    run()
# created on 2019-04-05
