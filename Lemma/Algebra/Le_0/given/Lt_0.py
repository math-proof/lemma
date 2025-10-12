from util import *


@apply
def apply(given):
    x = given.of(Expr <= 0)
    return x < 0


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x = Symbol(real=True)
    Eq << apply(x <= 0)

    Eq << Nat.Le.of.Lt.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2019-12-04
# updated on 2025-04-10
