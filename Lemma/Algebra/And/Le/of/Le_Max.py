from util import *


@apply
def apply(le, index=-1):
    args, x = le.of(Max <= Expr)
    first = args[:index]
    second = args[index:]

    return LessEqual(Max(*first), x), LessEqual(Max(*second), x)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Max(y, z) <= x)

    Eq << Algebra.Le.of.Le_Max.apply(Eq[0], index=0)

    Eq << Algebra.Le.of.Le_Max.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()
# created on 2019-11-29
