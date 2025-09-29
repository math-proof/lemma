from util import *


@apply
def apply(self):
    interval, (k, a, b) = self.of(Cup)
    S[k], S[k + 1] = interval.of(Interval)
    assert interval.left_open and not interval.right_open

    return Equal(self, Interval(a, b, left_open=True))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    k, a, b = Symbol(integer=True)
    Eq << apply(Cup[k:a:b](Interval(k, k + 1, left_open=True)))

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[0], cond=a < b)

    Eq << Eq[-2].this.lhs.apply(Set.Cup.eq.Icc.of.Lt.left_open, k)

    Eq << (a >= b).this.apply(Set.Eq_Empty.Icc.of.Ge, left_open=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Ufn.given.Eq.Ufn)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.find(Cup).apply(Set.Cup.eq.Cup_Ite)

    Eq << (a >= b).this.apply(Set.Eq_Empty.Range.of.Ge)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Eq.Ufn.given.Eq.Ufn)





if __name__ == '__main__':
    run()
# created on 2018-10-20
# updated on 2023-08-26
