from util import *


@apply
def apply(lt, le, right_open=False, left_open=False):
    a, x = lt.of(Less)
    S[x], b = le.of(LessEqual)
    return Equal(Interval(a, x, left_open=left_open) | Interval(x, b, left_open=True, right_open=right_open), Interval(a, b, left_open=left_open, right_open=right_open))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool, Nat

    a, b, x = Symbol(real=True, given=True)
    Eq << apply(a < x, x <= b)

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[2])

    Eq <<= Eq[-2].this.lhs.apply(Set.OrInS.of.In_Union), Eq[-1].this.rhs.apply(Set.In_Union.given.OrInS)

    Eq <<= Bool.ImpOr.given.Imp.Imp.apply(Eq[-2]), Eq[-1].this.apply(Bool.Imp.Is.ImpNotS)

    Eq <<= Eq[-3].this.lhs.apply(Set.Le.Le.of.In_Icc), Eq[-2].this.lhs.apply(Set.Le.Le.of.In_Icc), Eq[-1].this.lhs.args[0].apply(Set.Or.of.NotIn_Icc)

    Eq <<= Eq[-3].this.rhs.apply(Set.In_Ico.given.Le.Lt), Eq[-2].this.rhs.apply(Set.In_Ico.given.Le.Lt), Eq[-1].this.lhs.find(NotElement).apply(Set.Or.of.NotIn_Icc)

    Eq <<= Bool.Imp_And.of.Cond.apply(Eq[0], cond=Eq[-3].lhs), Bool.Imp_And.of.Cond.apply(Eq[1], cond=Eq[-2].lhs), Eq[-1].this.rhs.apply(Set.NotIn_Icc.given.OrLtS)

    Eq <<= Eq[-3].this.rhs.args[:2].apply(Nat.Ge.of.Lt.Gt), Eq[-2].this.rhs.args[:2].apply(Nat.Le.of.Le.Le),  Eq[-1].this.lhs.apply(Bool.OrAndS.of.And_Or)

    Eq << Bool.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq << Bool.ImpAnd.given.Imp.apply(Eq[-2])

    Eq << Bool.ImpAnd.given.Imp.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2018-10-13
# updated on 2023-05-12
