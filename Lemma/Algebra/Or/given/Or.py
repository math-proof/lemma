from util import *


@apply
def apply(imply, index=None):
    eqs = imply.of(Or)
    assert isinstance(index, slice)

    return Or(*eqs[index])


@prove
def prove(Eq):
    x, y, b = Symbol(real=True, given=True)
    f = Function(real=True)

    Eq << apply((f(y) > 0) | (f(x) > 0) | (f(b) > 0), index=slice(0, 2))

    Eq << ~Eq[0]

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

# created on 2019-07-08

