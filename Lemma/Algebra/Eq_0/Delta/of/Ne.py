from util import *


@apply(simplify=False)
def apply(given):
    lhs, rhs = given.of(Unequal)
    return Equal(KroneckerDelta(lhs, rhs), 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x, y = Symbol(integer=True, given=True)
    Eq << apply(Unequal(x, y))

    Eq << Eq[1].this.lhs.apply(Nat.Delta.eq.Ite)


if __name__ == '__main__':
    run()

# created on 2019-05-03
