from util import *


@apply
def apply(is_nonpositive, is_nonnegative):
    x = is_nonnegative.of(Expr >= 0)
    S[x] = is_nonpositive.of(Expr <= 0)
    return Equal(x, 0)


@prove
def prove(Eq):
    x = Symbol(real=True)

    Eq << apply(x <= 0, x >= 0)

    Eq <<= Eq[0] & Eq[1]

    Eq << Eq[-1].simplify()


if __name__ == '__main__':
    run()
# created on 2018-07-14
