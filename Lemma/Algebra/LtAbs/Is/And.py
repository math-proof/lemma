from util import *


@apply
def apply(lt):
    x, a = lt.of(Abs < Expr)
    assert x.is_extended_real
    return And(Less(x, a), Greater(x, -a))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x, a = Symbol(real=True, given=True)
    Eq << apply(abs(x) < a)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.And.of.LtAbs)

    Eq << Eq[-1].this.rhs.apply(Algebra.LtAbs.given.And)




if __name__ == '__main__':
    run()
# created on 2022-01-07
