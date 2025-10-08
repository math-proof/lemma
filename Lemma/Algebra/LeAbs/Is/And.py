from util import *


@apply
def apply(le):
    abs_x, a = le.of(LessEqual)
    x = abs_x.of(Abs)
    return And(LessEqual(x, a), GreaterEqual(x, -a))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    x, a = Symbol(integer=True, given=True)
    Eq << apply(abs(x) <= a)

    Eq << Bool.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.And.of.LeAbs)

    Eq << Eq[-1].this.rhs.apply(Algebra.LeAbs.given.And)




if __name__ == '__main__':
    run()
# created on 2022-01-07
