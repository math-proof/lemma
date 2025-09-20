from util import *


@apply
def apply(given):
    x, y = given.of(Expr - Expr <= 0)
    return GreaterEqual(y, x)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    a, b = Symbol(real=True, given=True)
    Eq << apply(GreaterEqual(0, a - b))

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Ge.of.Le_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Le_0.given.Ge)


if __name__ == '__main__':
    run()
# created on 2023-06-20
