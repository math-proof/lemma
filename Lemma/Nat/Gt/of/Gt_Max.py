from util import *


@apply
def apply(gt, index=0):
    x, args = gt.of(Expr > Max)
    y = args[index]

    return Greater(x, y)


@prove
def prove(Eq):
    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x > Max(y, z))

    Eq << ~Eq[1]

    # Eq <<= Eq[-1] & Eq[0]
    Eq <<= Eq[0] & Eq[-1]


if __name__ == '__main__':
    run()
# created on 2019-08-03
