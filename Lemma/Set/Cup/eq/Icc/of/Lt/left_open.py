from util import *


@apply
def apply(lt, k=None):
    a, b = lt.of(Less)
    assert a.is_integer and b.is_integer
    if k is None:
        k = lt.generate_var(integer=True)
    return Equal(Cup[k:a:b](Interval(k, k + 1, left_open=True)), Interval(a, b, left_open=True))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    a, b, k = Symbol(integer=True)
    Eq << apply(a < b, k)

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[1], cond=a >= 0)

    Eq <<= Logic.Imp.And.of.Cond.apply(Eq[0], cond=Eq[-2].lhs), Logic.Imp.And.of.Cond.apply(Eq[0], cond=Eq[-1].lhs)

    Eq <<= Eq[-2].this.rhs.apply(Set.Cup.eq.Icc.of.Ge_0.Lt.left_open), Eq[-1].this.rhs.apply(Set.Cup.eq.Icc.of.Lt_0.Lt.left_open)


if __name__ == '__main__':
    run()
# created on 2018-10-16
