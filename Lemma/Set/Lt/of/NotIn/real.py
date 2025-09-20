from util import *


@apply
def apply(given):
    n, a = given.of(NotElement[Interval[Infinity]])

    return Less(n, a)


@prove
def prove(Eq):
    x, a = Symbol(real=True, given=True)

    Eq << apply(NotElement(x, Interval(a, oo)))

    Eq << ~Eq[-1]

    Eq <<= Eq[-1] & Eq[0]

    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    run()

# created on 2021-08-31
