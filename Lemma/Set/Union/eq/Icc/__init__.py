from util import *


@apply
def apply(self):
    int0, int1 = self.of(Union)
    assert int1.left_open == int1.right_open == int0.left_open == int0.right_open
    a, b = int0.of(Interval)
    S[b], S[a] = int1.of(Interval)
    if int1.left_open:
        func = Interval.open
    else:
        func = Interval

    return Equal(self, func(Min(a, b), Max(b, a)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    a, b = Symbol(real=True)
    Eq << apply(Interval(a, b) | Interval(b, a))

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[0], cond=a > b)

    Eq << Imply(a > b, Equal(Min(a, b), b), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.EqMin.of.Gt)

    Eq <<= Eq[1] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Ufn.given.Eq.Ufn)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Imply(a > b, Equal(Max(a, b), a), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.EqMax.of.Gt)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Ufn.given.Eq.Ufn)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Imply(a > b, Equal(Interval(a, b), a.emptySet), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Set.Icc.eq.Empty.of.Gt)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Ufn.given.Eq.Ufn)

    Eq << Imply(a <= b, Equal(Max(a, b), b), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.EqMax.of.Le)

    Eq <<= Eq[2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Ufn.given.Eq.Ufn)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Imply(a <= b, Equal(Min(a, b), a), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Algebra.EqMin.of.Le)

    Eq <<= Eq[-2] & Eq[-1]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Ufn.given.Eq.Ufn)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Imply(a <= b, Subset(Interval(b, a), Interval(a, b)), plausible=True)

    Eq << Eq[-1].this.lhs.apply(Set.Subset.Icc.of.Le)

    Eq << Eq[-1].this.rhs.apply(Set.EqUnion.of.Subset)





if __name__ == '__main__':
    run()
# created on 2020-06-04
# updated on 2023-08-26
del Abs
from . import Abs
from . import of
