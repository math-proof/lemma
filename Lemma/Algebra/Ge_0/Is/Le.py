from util import *


@apply
def apply(given):
    x, y = given.of(Expr - Expr >= 0)
    return LessEqual(y, x)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    a, b = Symbol(real=True, given=True)
    Eq << apply(LessEqual(0, a - b))

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Le.of.Ge_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge_0.given.Le)


if __name__ == '__main__':
    run()
# created on 2023-06-20
