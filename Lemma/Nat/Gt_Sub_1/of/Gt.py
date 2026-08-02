from util import *


@apply
def apply(given, lower=None, upper=None):
    lhs, rhs = given.of(Greater)
    if lower is not None:
        assert lower <= rhs
        rhs = lower
    elif upper is not None:
        assert upper >= lhs
        lhs = upper

    return Greater(lhs, rhs)


@prove
def prove(Eq):
    x, y = Symbol(real=True, given=True)
    Eq << apply(Greater(x, y), y - 1)

    Eq << ~Eq[-1]

    Eq <<= Eq[0] & Eq[-1]

    # Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2018-07-05
