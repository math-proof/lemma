from util import *


@apply
def apply(self):
    interval, (k, n, S[0]) = self.of(Cup)
    S[k], S[k + 1] = interval.of(Interval)
    assert interval.left_open and not interval.right_open
    assert n <= 0

    return Equal(self, Interval(n, 0, left_open=True))


@prove
def prove(Eq):
    from Lemma import Set

    n = Symbol(integer=True, nonnegative=True)
    k = Symbol(integer=True)
    Eq << apply(Cup[k:-n:0](Interval(k, k + 1, left_open=True)))

    Eq << Eq[-1].this.lhs.apply(Set.Cup.limits.subst.Neg, k, -1 - k)

    Eq << Eq[-1].this.lhs.apply(Set.Cup.eq.Icc.induct.negative.left_open)


if __name__ == '__main__':
    run()
# created on 2018-10-08
