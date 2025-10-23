from util import *


@apply
def apply(given):
    lhs, rhs = given.of(GreaterEqual)
    assert lhs.is_integer
    return Greater(lhs, rhs - 1)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Nat, Nat

    x, y = Symbol(integer=True)
    Eq << apply(x >= y)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Nat.Gt_Sub_1.of.Ge)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge.given.Gt.relax)


if __name__ == '__main__':
    run()
# created on 2023-11-05
