from util import *


@apply
def apply(given):
    x = given.of(Expr < 0)

    return LessEqual(Ceil(x), 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True)
    Eq << apply(x < 0)

    Eq << Algebra.Le.of.Lt.apply(Eq[0])

    Eq << Algebra.Ceil.le.Zero.of.Le_0.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2020-01-18
# updated on 2025-04-10
