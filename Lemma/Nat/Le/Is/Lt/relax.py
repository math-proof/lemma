from util import *


@apply
def apply(given):
    lhs, rhs = given.of(LessEqual)
    assert lhs.is_integer
    return Less(lhs, rhs + 1)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat

    x, y = Symbol(integer=True)
    Eq << apply(x <= y)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Nat.Lt_Add_1.of.Le)

    Eq << Eq[-1].this.rhs.apply(Nat.Le.given.Lt.relax)


if __name__ == '__main__':
    run()
# created on 2023-11-05
