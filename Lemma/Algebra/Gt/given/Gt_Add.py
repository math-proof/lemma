from util import *


@apply
def apply(given, upper):
    lhs, rhs = given.of(Greater)

    assert upper >= rhs

    return Greater(lhs, upper)


@prove
def prove(Eq):
    x, y = Symbol(real=True, given=True)
    Eq << apply(Greater(x, y), y + 1)

    Eq << ~Eq[0]

    # Eq <<= Eq[1] & Eq[-1]
    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

# created on 2018-03-26
