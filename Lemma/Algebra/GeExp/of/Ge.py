from util import *


@apply
def apply(given):
    lhs, rhs = given.of(GreaterEqual)

    return GreaterEqual(exp(lhs), exp(rhs))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    Eq << apply(GreaterEqual(x, y))

    Eq << Algebra.LeExp.of.Le.apply(Eq[0].reversed).reversed




if __name__ == '__main__':
    run()
# created on 2023-04-16
