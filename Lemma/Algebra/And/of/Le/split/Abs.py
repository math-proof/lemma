from util import *


@apply
def apply(given):
    abs_x, a = given.of(LessEqual)
    x = abs_x.of(Abs)
    return LessEqual(x, a), GreaterEqual(x, -a)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a = Symbol(integer=True, given=True)
    Eq << apply(abs(x) <= a)

    Eq << Algebra.Le.of.Le.split.Abs.apply(Eq[0])

    Eq << -Algebra.Le.of.Le.split.Abs.apply(Eq[0], negate=True)




if __name__ == '__main__':
    run()
# created on 2023-04-15
