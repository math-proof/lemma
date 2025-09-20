from util import *


@apply
def apply(le, index=-1):
    x, args = le.of(Expr <= Min)
    first = args[:index]
    second = args[index:]

    return x <= Min(*first), x <= Min(*second)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x <= Min(y, z))

    Eq << Algebra.LeMin.of.Le.Le.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()
# created on 2022-01-01
