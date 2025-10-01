from util import *


@apply
def apply(le, _le, right_open=True, left_open=None):
    x, a = le.of(LessEqual)
    b, _x = _le.of(LessEqual)
    if x != _x:
        a, x, S[x], b = _x, b, a, x,
    if left_open is not None:
        right_open = not left_open
    return Equal(Interval(b, x, right_open=right_open) | Interval(x, a, left_open=not right_open), Interval(b, a))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    a, b, x = Symbol(real=True, given=True)
    Eq << apply(x <= b, a <= x)

    Eq << Set.Eq.given.All_Imp.All_Imp.apply(Eq[2])

    Eq <<= Eq[-2].this.lhs.apply(Set.OrInS.of.In_Union), Eq[-1].this.rhs.apply(Set.In_Union.given.OrInS)

    Eq <<= Logic.ImpOr.given.Imp.Imp.apply(Eq[-2]), Eq[-1].this.apply(Logic.Imp.Is.ImpNotS)

    Eq <<= Eq[-3].this.lhs.apply(Set.Ge.Le.of.In_Icc), Eq[-2].this.lhs.apply(Set.Ge.Le.of.In_Icc), Eq[-1].this.lhs.args[0].apply(Set.Or.of.NotIn_Icc)

    Eq <<= Eq[-3].this.rhs.apply(Set.In_Ico.given.Ge.Lt), Eq[-2].this.rhs.apply(Set.In_Ico.given.Ge.Lt), Eq[-1].this.lhs.find(NotElement).apply(Set.Or.of.NotIn_Icc)

    Eq <<= Logic.Imp_And.of.Cond.apply(Eq[0], cond=Eq[-3].lhs), Logic.Imp_And.of.Cond.apply(Eq[1], cond=Eq[-2].lhs), Eq[-1].this.rhs.apply(Set.NotIn_Icc.given.OrLtS)

    Eq <<= Eq[-3].this.rhs.args[:2].apply(Algebra.Le.of.Le.Lt.relax), Eq[-2].this.rhs.args[::2].apply(Algebra.Ge.of.Le.Ge),  Eq[-1].this.lhs.apply(Logic.OrAndS.of.And_Or)

    Eq << Logic.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq << Logic.ImpAnd.given.Imp.apply(Eq[-2])

    Eq << Logic.ImpAnd.given.Imp.apply(Eq[-1])





if __name__ == '__main__':
    run()
# created on 2021-05-23
# updated on 2023-05-12

