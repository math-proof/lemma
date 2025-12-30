from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple])
    S[k], S[k + 1] = interval.of(Interval)
    assert interval.left_open and not interval.right_open

    return Equal(self, Interval(-oo, oo, left_open=True))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    k = Symbol(integer=True)
    Eq << apply(Cup[k](Interval(k, k + 1, left_open=True)))

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[0])

    x = Eq[-1].lhs
    Eq <<= Set.In_Cup.given.Any_In.apply(Eq[-1])

    Eq << Algebra.Any.given.Cond.subst.apply(Eq[-1], Eq[-1].variable, Ceil(x) - 1)

    Eq << Set.In_Ico.given.Le.Lt.apply(Eq[-1])

    Eq << Algebra.Gt_Sub_.Ceil.One.apply(x)

    Eq << Algebra.Le_Ceil.apply(x)


if __name__ == '__main__':
    run()
# created on 2021-02-18
