from util import *


@apply
def apply(self):
    interval, k = self.of(Cup[Tuple[0, oo]])
    _k1, _k = interval.of(Interval)
    assert _k1 == -k - 1 and _k == -k
    assert not interval.left_open and interval.right_open

    return Equal(self, Interval.open(-oo, 0))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    k = Symbol(integer=True)
    Eq << apply(Cup[k:oo](Interval(-k - 1, -k, right_open=True)))

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[0])

    Eq <<= Eq[-2].this.lhs.apply(Set.Any_In.of.In_Cup), Eq[-1].this.rhs.apply(Set.In_Cup.given.Any_In)

    k = Eq[-1].rhs.variable
    x = Eq[-1].lhs.lhs
    Eq <<= Eq[-2].this.lhs.expr.apply(Set.Lt.of.In_Icc), Eq[-1].this.rhs.apply(Algebra.Any.given.Cond.subst, k, -Floor(x) - 1)

    Eq <<= Eq[-2].this.lhs.apply(Bool.Any_And.of.AnySetOf_AnySetOf, simplify=None), Bool.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-3].this.lhs.find(Element).apply(Set.Le.of.In_Ico), Eq[-1].this.rhs.apply(Set.In_Ico.given.And), Bool.Imp.given.Cond.apply(Eq[-2])

    Eq <<= Eq[-3].this.lhs.expr.apply(Algebra.LtAdd.of.Le.Lt), Eq[-2].this.rhs.apply(Algebra.Ge.transport, lhs=0), Set.In_Ico.given.Le.Lt.apply(Eq[-1])

    Eq << Eq[-4].this.lhs.apply(Set.IsNegative.of.Lt_0, simplify=None)

    Eq << Algebra.Ge_Floor.apply(x)

    Eq << Algebra.Lt_Add_.Floor.One.apply(x)

    Eq << -Eq[-3].this.rhs

    Eq << Eq[-1].this.rhs.apply(Algebra.Le.given.Lt.One)

    Eq << Eq[-1].this.lhs.apply(Set.Lt.of.In_Icc)

    Eq << Eq[-1].this.lhs.apply(Algebra.Floor.lt.Zero.of.Lt_0)



if __name__ == '__main__':
    run()
# created on 2021-02-17
# updated on 2023-05-14
