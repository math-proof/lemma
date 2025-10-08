from util import *


@apply
def apply(given):
    x = given.of(Expr >= 0)
    return sqrt(x) >= 0


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.GeSqrt_0.of.Ge_0)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ge_0.given.Ge_0.Sqrt)


if __name__ == '__main__':
    run()
# created on 2023-06-20
