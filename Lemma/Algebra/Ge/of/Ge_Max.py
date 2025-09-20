from util import *


@apply
def apply(given, index=0):
    x, args = given.of(Expr >= Max)
    y = args[index]

    return GreaterEqual(x, y)


@prove
def prove(Eq):
    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x >= Max(y, z))

    Eq << ~Eq[1]

    # Eq <<= Eq[-1] & Eq[0]

    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-06-05
