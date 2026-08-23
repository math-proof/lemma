from util import *


@apply
def apply(given, index=0):
    args, x = given.of(Min > Expr)
    y = args[index]

    return Greater(y, x)


@prove
def prove(Eq):
    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Min(y, z) > x)

    Eq << ~Eq[1]

    # Eq <<= Eq[-1] & Eq[0]

    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-08-04
