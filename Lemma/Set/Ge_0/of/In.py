from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    a, b = R.of(Interval)
    assert a >= 0

    assert x.is_complex
    return GreaterEqual(x, 0)


@prove
def prove(Eq):
    x = Symbol(complex=True, given=True)
    Eq << apply(Element(x, Interval(0, oo)))

    Eq << ~Eq[1]

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2021-09-03
