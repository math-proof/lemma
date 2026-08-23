from util import *


@apply
def apply(given, bound):
    lhs, rhs = given.of(LessEqual)

    assert bound <= rhs

    return LessEqual(lhs, bound)


@prove
def prove(Eq):
    x, y = Symbol(real=True, given=True)
    Eq << apply(LessEqual(x, y), y - 1)

    Eq << ~Eq[0]

    # Eq <<= Eq[1] & Eq[-1]
    Eq <<= Eq[-1] & Eq[1]


if __name__ == '__main__':
    run()

# created on 2021-08-11
