from util import *


@apply
def apply(given):
    a, b = given.of(GreaterEqual)
    return Equal(Interval(a, b), a.set & b.set)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    x, y = Symbol(real=True, given=True)
    Eq << apply(x >= y)

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=x > y)

    Eq.is_zero = (x > y).this.apply(Set.Icc.eq.Empty.of.Gt)

    Eq << Set.InterSingletonS.subset.Icc.apply(x, y)

    Eq << Bool.Imp_And.of.Cond.Imp.apply(Eq[-1], Eq.is_zero)

    Eq << Eq[-1].this.rhs.apply(Bool.Cond.of.Eq.Cond.subst)

    Eq << Eq[-1].this.rhs.apply(Set.EqEmpty.of.Subset_Empty, simplify=None)

    Eq <<= Eq[-1] & Eq.is_zero

    Eq << Eq[-1].this.rhs.apply(Bool.Eq.of.Eq.Eq)

    Eq << Imply(x <= y, Equal(x, y), plausible=True)

    Eq << Bool.Imp.given.Or_Not.apply(Eq[-1])

    Eq <<= Eq[3] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Ufn.given.Eq.Ufn)





if __name__ == '__main__':
    run()
# created on 2018-09-15
# updated on 2023-08-26
