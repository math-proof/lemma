from util import *


@apply
def apply(is_negative, lt, k=None):
    a = is_negative.of(Expr < 0)
    S[a], b = lt.of(Less)

    assert a.is_integer and b.is_integer
    if k is None:
        k = lt.generate_var(integer=True)
    return Equal(Cup[k:a:b](Interval(k, k + 1, left_open=True)), Interval(a, b, left_open=True))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    a, b, k = Symbol(integer=True)
    Eq << apply(a < 0, a < b, k)

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=b >= 0)

    Eq <<= Bool.Imp_And.of.Cond.apply(Eq[0], cond=Eq[-2].lhs), Bool.Imp_And.of.Cond.apply(Eq[0] & Eq[1], cond=Eq[-1].lhs)

    Eq << Eq[-2].this.rhs.apply(Set.Cup.eq.Icc.of.Lt_0.Ge_0.left_open)

    Eq << Eq[-1].this.rhs.apply(Set.Cup.eq.Icc.of.Lt_0.Lt_0.Lt.left_open)





if __name__ == '__main__':
    run()
# created on 2018-10-15
# updated on 2021-11-23
