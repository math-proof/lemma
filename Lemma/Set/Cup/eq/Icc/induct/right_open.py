from util import *


@apply
def apply(self):
    interval, (k, S[0], n) = self.of(Cup)
    S[k], S[k + 1] = interval.of(Interval)
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval(0, n, right_open=True))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    n = Symbol(integer=True, positive=True, given=False)
    k = Symbol(integer=True)
    Eq << apply(Cup[k:n](Interval(k, k + 1, right_open=True)))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(Set.Cup.eq.UnionCupS, cond={n})

    Eq << Set.EqUnionS.of.Eq.apply(Eq[0], Interval(n, n + 1, right_open=True))

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Eq_Ite.of.All_Imp.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()
# created on 2021-02-12
