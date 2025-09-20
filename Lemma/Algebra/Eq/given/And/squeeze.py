from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Equal)
    return lhs <= rhs, lhs >= rhs


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    Eq << apply(Equal(x, y))

    Eq << Algebra.Eq.of.Le.Ge.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-03-30
