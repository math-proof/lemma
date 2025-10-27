from util import *


@apply
def apply(self):
    interval, (k, a, b) = self.of(Cup)
    S[k], S[k + 1] = interval.of(Interval)
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval(a, b, right_open=True))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool, Nat

    k, a, b = Symbol(integer=True)
    Eq << apply(Cup[k:a:b](Interval(k, k + 1, right_open=True)))

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[0], cond=a < b)

    Eq << Eq[-2].this.lhs.apply(Set.Cup.eq.Icc.of.Lt.right_open, k)

    Eq << (a >= b).this.apply(Set.Eq_Empty.Icc.of.Ge, right_open=True)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Nat.Eq.UnaryFn.given.Eq.UnaryFn)

    Eq << Bool.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[-1].this.find(Cup).apply(Set.Cup.eq.Cup_Ite)

    Eq << (a >= b).this.apply(Set.Eq_Empty.Ico.of.Ge)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Nat.Eq.UnaryFn.given.Eq.UnaryFn)





if __name__ == '__main__':
    run()
# created on 2021-02-23
# updated on 2023-08-26

from . import negative
