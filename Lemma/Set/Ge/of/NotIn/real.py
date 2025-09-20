from util import *


@apply
def apply(given):
    n, b = given.of(NotElement[Interval[NegativeInfinity]])
    return GreaterEqual(n, b)


@prove
def prove(Eq):
    x, a = Symbol(real=True, given=True)

    Eq << apply(NotElement(x, Interval.open(-oo, a)))

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]

    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    run()

# created on 2021-09-21
