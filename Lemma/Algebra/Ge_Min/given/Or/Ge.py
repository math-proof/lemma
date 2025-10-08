from util import *


@apply
def apply(given, index=-1):
    x, args = given.of(Expr >= Min)
    first = args[:index]
    second = args[index:]

    return GreaterEqual(x, Min(*first)) | GreaterEqual(x, Min(*second))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x >= Min(y, z))

    Eq << ~Eq[0]

    Eq <<= Eq[-1] & Eq[1]

    Eq << Eq[-1].this.apply(Bool.OrAndS.of.And_Or)


if __name__ == '__main__':
    run()
# created on 2022-01-02
