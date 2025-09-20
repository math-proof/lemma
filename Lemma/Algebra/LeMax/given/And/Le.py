from util import *


@apply
def apply(ge, index=-1):
    args, x = ge.of(Max <= Expr)
    first = args[:index]
    second = args[index:]

    return Max(*first) <= x, Max(*second) <= x


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Max(y, z) <= x)

    Eq << Algebra.LeMax.of.Le.Le.apply(Eq[1], Eq[2])




if __name__ == '__main__':
    run()
# created on 2023-03-26
