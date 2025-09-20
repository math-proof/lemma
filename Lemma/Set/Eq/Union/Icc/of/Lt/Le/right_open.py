from util import *


@apply
def apply(lt, le, right_open=False, left_open=False):
    a, x = lt.of(Less)
    S[x], b = le.of(LessEqual)
    return Equal(Interval(a, x, left_open=left_open, right_open=True) | Interval(x, b, right_open=right_open), Interval(a, b, left_open=left_open, right_open=right_open))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    a, b, x = Symbol(real=True, given=True)
    Eq << apply(a < x, x <= b, left_open=True)

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[2])

    Eq <<= Eq[-2].this.lhs.apply(Set.OrInS.of.In_Union), Eq[-1].this.rhs.apply(Set.In_Union.given.OrInS)

    Eq <<= Logic.ImpOr.given.Imp.Imp.apply(Eq[-2]), Eq[-1].this.apply(Logic.Imp.contraposition)

    Eq <<= Eq[-3].this.lhs.apply(Set.Ge.Le.of.In_Icc), Eq[-2].this.lhs.apply(Set.Ge.Le.of.In_Icc), Eq[-1].this.lhs.args[0].apply(Set.Or.of.NotIn_Icc)

    Eq <<= Eq[-3].this.rhs.apply(Set.In_Ico.given.Ge.Lt), Eq[-2].this.rhs.apply(Set.In_Ico.given.Ge.Lt), Eq[-1].this.lhs.find(NotElement).apply(Set.Or.of.NotIn_Icc)

    Eq <<= Logic.Imp.And.of.Cond.apply(Eq[1], cond=Eq[-3].lhs), Logic.Imp.And.of.Cond.apply(Eq[0], cond=Eq[-2].lhs), Eq[-1].this.rhs.apply(Set.NotIn_Icc.given.Or)

    Eq <<= Eq[-3].this.rhs.args[::2].apply(Algebra.Le.of.Le.Lt.relax), Eq[-2].this.rhs.args[::2].apply(Algebra.Gt.of.Lt.Ge),  Eq[-1].this.lhs.apply(Logic.OrAndS.of.And_Or)

    Eq << Logic.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq << Logic.Imp.given.Imp.split.And.apply(Eq[-1])

    Eq << Logic.Imp.given.Imp.split.And.apply(Eq[-2], 1)





if __name__ == '__main__':
    run()
# created on 2021-02-20
# updated on 2023-05-14
