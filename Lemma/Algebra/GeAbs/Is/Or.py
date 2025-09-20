from util import *


@apply
def apply(ge):
    x, a = ge.of(Abs >= Expr)
    return Or(x <= -a, x >= a)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) >= a)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Or.of.GeAbs)

    Eq << Eq[-1].this.rhs.apply(Algebra.GeAbs.given.Or)


if __name__ == '__main__':
    run()
# created on 2022-01-07
