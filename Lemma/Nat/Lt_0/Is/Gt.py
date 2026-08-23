from util import *


@apply
def apply(given):
    x, y = given.of(Expr - Expr < 0)
    return Greater(y, x)


@prove
def prove(Eq):
    from Lemma import Bool, Nat

    a, b = Symbol(real=True, given=True)
    Eq << apply(Greater(0, a - b))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Nat.Gt.of.Lt_0)

    Eq << Eq[-1].this.rhs.apply(Nat.Lt_0.given.Gt)


if __name__ == '__main__':
    run()
# created on 2023-06-20
