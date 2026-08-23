from util import *


@apply
def apply(given, index=-1):
    args, x = given.of(Min >= Expr)
    first = args[:index]
    second = args[index:]

    return GreaterEqual(Min(*first), x), GreaterEqual(Min(*second), x)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Min(y, z) >= x)

    Eq << Algebra.Ge.of.Ge_Min.apply(Eq[0], index=0)

    Eq << Algebra.Ge.of.Ge_Min.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()
# created on 2019-06-08
