from util import *


@apply
def apply(self):
    interval, (k, S[0], n) = self.of(Cup)
    S[-k - 1], S[-k] = interval.of(Interval)
    assert interval.left_open and not interval.right_open
    assert n >= 0
    return Equal(self, Interval(-n, 0, left_open=True))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    n = Symbol(integer=True, nonnegative=True, given=False)
    k = Symbol(integer=True)
    Eq << apply(Cup[k:n](Interval(-k - 1, -k, left_open=True)))

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.lhs.apply(Set.Cup.eq.UnionCupS, cond={n})

    Eq << Set.EqUnionS.of.Eq.apply(Eq[0], Interval(-n - 1, -n, left_open=True))

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Logic.Eq_Ite.of.All_Imp.apply(Eq[-1], n=n, start=0)


if __name__ == '__main__':
    run()
# created on 2018-10-07
