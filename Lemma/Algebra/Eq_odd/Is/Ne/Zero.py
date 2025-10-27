from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 1])
    return Unequal(n % 2, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat

    n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 1))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Nat.Ne_0.of.Eq)

    Eq << Eq[-1].this.lhs.apply(Algebra.Eq_odd.of.Ne_0)


if __name__ == '__main__':
    run()
# created on 2023-05-30
