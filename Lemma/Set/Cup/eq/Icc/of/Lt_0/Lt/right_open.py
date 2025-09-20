from util import *


@apply
def apply(is_negative, lt, k=None):
    a = is_negative.of(Expr < 0)
    S[a], b = lt.of(Less)

    assert a.is_integer and b.is_integer
    if k is None:
        k = lt.generate_var(integer=True)
    return Equal(Cup[k:a:b](Interval(k, k + 1, right_open=True)), Interval(a, b, right_open=True))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    a, b, k = Symbol(integer=True)
    Eq << apply(a < 0, a < b, k)

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=b >= 0)

    Eq <<= Logic.Imp.And.of.Cond.apply(Eq[0], cond=Eq[-2].lhs), Logic.Imp.And.of.Cond.apply(Eq[0] & Eq[1], cond=Eq[-1].lhs)

    Eq << Eq[-2].this.rhs.apply(Set.Cup.eq.Icc.of.Lt_0.Ge_0.right_open)

    Eq << Eq[-1].this.rhs.apply(Set.Cup.eq.Icc.of.Lt_0.Lt_0.Lt.right_open)





if __name__ == '__main__':
    run()
# created on 2021-02-22
# updated on 2021-11-23
