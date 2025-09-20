from util import *


@apply
def apply(given):
    x, b = given.of(GreaterEqual)
    assert x <= b
    return Equal(x, b)


@prove
def prove(Eq):
    a = Symbol(real=True)
    b = Symbol(real=True, given=True)
    x = Symbol(domain=Interval(a, b), given=True)
    Eq << apply(x >= b)

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]




if __name__ == '__main__':
    run()

# created on 2020-05-07
# updated on 2023-11-11

