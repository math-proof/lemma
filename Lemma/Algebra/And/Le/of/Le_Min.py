from util import *


@apply
def apply(le, index=-1):
    x, args = le.of(Expr <= Min)
    first = args[:index]
    second = args[index:]

    return LessEqual(x, Min(*first)), LessEqual(x, Min(*second))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x <= Min(y, z))

    Eq << Algebra.Le.of.Le_Min.apply(Eq[0], index=0)

    Eq << Algebra.Le.of.Le_Min.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()
# created on 2019-11-30
