from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple])
    S[k], S[k + 1] = interval.of(Interval)
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval.open(-oo, oo))


@prove
def prove(Eq):
    from Lemma import Set

    k = Symbol(integer=True)
    Eq << apply(Cup[k](Interval(k, k + 1, right_open=True)))

    Eq << Eq[0].this.lhs.apply(Set.Cup.eq.UnionCupS, cond=k >= 0)

    Eq << Eq[-1].this.find(Cup | ~Cup).apply(Set.CupIn_Ico.eq.Cup_UFnSub, k, -k - 1)

    Eq << Eq[-1].this.find(Cup).apply(Set.Cup.eq.Icc.Infty.right_open)

    Eq << Eq[-1].this.find(Cup).apply(Set.Cup.eq.Icc.NegInfty.right_open)





if __name__ == '__main__':
    run()
# created on 2021-02-18
# updated on 2023-05-13
