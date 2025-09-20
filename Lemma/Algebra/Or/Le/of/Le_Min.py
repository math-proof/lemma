from util import *


@apply
def apply(given, index=-1):
    args, x = given.of(Min <= Expr)
    first = args[:index]
    second = args[index:]

    return LessEqual(Min(*first), x) | LessEqual(Min(*second), x)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Min(y, z) <= x)

    Eq << ~Eq[1]

    Eq << Eq[-1].this.apply(Algebra.GtMin.of.Gt.Gt)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()
# created on 2022-01-02
