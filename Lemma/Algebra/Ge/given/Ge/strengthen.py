from util import *


@apply
def apply(given, bound):
    lhs, rhs = given.of(GreaterEqual)

    assert bound >= rhs

    return GreaterEqual(lhs, bound)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(GreaterEqual(x, y), y + 1)



    Eq << Algebra.Ge.of.Ge.relax.apply(Eq[1], lower=y)




if __name__ == '__main__':
    run()

# created on 2021-07-29
# updated on 2023-10-03
