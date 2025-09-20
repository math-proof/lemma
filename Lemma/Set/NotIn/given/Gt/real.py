from util import *


@apply
def apply(given):
    n, s = given.of(NotElement)
    b, a = s.of(Interval)
    assert b < a
    return Greater(n, a)


@prove
def prove(Eq):
    x, a = Symbol(real=True, given=True)
    Eq << apply(NotElement(x, Interval(-oo, a)))

    Eq << ~Eq[0]

    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

# created on 2021-09-03
