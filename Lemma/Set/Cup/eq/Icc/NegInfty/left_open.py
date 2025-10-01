from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple[0, oo]])
    _k1, _k = interval.of(Interval)
    assert _k1 == -k - 1 and _k == -k
    assert interval.left_open and not interval.right_open

    return Equal(self, Interval(-oo, 0))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    k = Symbol(integer=True)
    Eq << apply(Cup[k:oo](Interval(-k - 1, -k, left_open=True)))

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.Any_In.of.In_Cup), Eq[-1].this.rhs.apply(Set.In_Cup.given.Any_In)

    k = Eq[-1].rhs.variable
    x = Eq[-1].lhs.lhs
    Eq <<= Eq[-2].this.lhs.expr.apply(Set.Ge.of.In_Icc), Eq[-1].this.rhs.apply(Algebra.Any.given.Cond.subst, k, -Ceil(x))

    Eq <<= Eq[-2].this.lhs.apply(Logic.Any_And.of.AnySetOf_AnySetOf, simplify=None), Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.find(Element).apply(Set.Ge.of.In_Ico), Eq[-1].this.rhs.apply(Set.In_Ico.given.And), Logic.Imp.given.Cond.apply(Eq[-2])

    Eq <<= Eq[-3].this.lhs.expr.apply(Algebra.GeAdd.of.Ge.Ge), -Eq[-2].this.rhs, Set.In_Ico.given.Ge.Lt.apply(Eq[-1])

    Eq << Eq[-4].this.lhs.apply(Set.IsNotPositive.of.Le_0, simplify=None)

    Eq << Algebra.Gt_Sub_.Ceil.One.apply(x)

    Eq << Eq[-3].this.lhs.apply(Set.Le.of.In_Icc)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ceil.le.Zero.of.Le_0)

    Eq << Algebra.Le_Ceil.apply(x)





if __name__ == '__main__':
    run()
# created on 2021-02-16
# updated on 2023-05-19
