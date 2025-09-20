from util import *


@apply
def apply(given, index=-1):
    x, args = given.of(Expr >= Max)
    first = args[:index]
    second = args[index:]

    return GreaterEqual(x, Max(*first)), GreaterEqual(x, Max(*second))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x >= Max(y, z))

    Eq << Algebra.Ge.of.Ge_Max.apply(Eq[0], index=0)

    Eq << Algebra.Ge.of.Ge_Max.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()
# created on 2019-06-06
