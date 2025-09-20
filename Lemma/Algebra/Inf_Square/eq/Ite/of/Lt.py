from util import *


@apply
def apply(lt, left_open=True, right_open=True, x=None):
    m, M = lt.of(Less)
    if x is None:
        x = lt.generate_var(real=True)

    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, Piecewise((0, (m <= 0) & (M >= 0)), (Min(m ** 2, M ** 2), True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m < M, x=x)

    Eq <<= Logic.Imp.And.of.Cond.apply(Eq[0], cond=m >= 0), Logic.Imp.And.of.Cond.apply(Eq[0], cond=M <= 0)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Inf_Square.eq.Square.of.Ge_0.Lt), Eq[-2].this.rhs.apply(Algebra.EqMin.of.Ge_0.Lt), \
        Eq[-1].this.rhs.apply(Algebra.Inf_Square.eq.Square.of.Le_0.Lt), Eq[-1].this.rhs.apply(Algebra.EqMin.of.Le_0.Lt)

    Eq <<= Eq[-3] & Eq[-4], Eq[-1] & Eq[-2]

    Eq <<= Eq[-2].this.rhs.apply(Logic.UFn.of.UFn.Eq, reverse=True), Eq[-1].this.rhs.apply(Logic.UFn.of.UFn.Eq, reverse=True)

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[1], cond=M >= 0)

    Eq <<= Logic.Imp.given.Imp.subst.Bool.apply(Eq[-2]), Logic.Imp.given.Imp.subst.Bool.apply(Eq[-1], invert=True)

    Eq <<= Eq[-1].this.lhs.apply(Algebra.Le.of.Lt), Logic.Cond.given.Imp.ImpNot.apply(Eq[-2], cond=m <= 0)

    Eq <<= Logic.Imp.given.Imp.subst.Bool.apply(Eq[-2]), Logic.Imp.given.Imp.subst.Bool.apply(Eq[-1], invert=True)

    Eq <<= Eq[-2].this.apply(Logic.Imp.flatten), Eq[-1].this.apply(Logic.Imp.flatten)

    Eq <<= Logic.Cond.given.Imp.ImpNot.apply(Eq[-2], cond=M > 0), Logic.Imp_And.given.Imp.delete.apply(Eq[-1], 1)

    Eq <<= Eq[-3].this.apply(Logic.Imp.flatten), Eq[-2].this.apply(Logic.Imp.flatten), Eq[-1].this.lhs.apply(Algebra.Ge.of.Gt.relax)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Inf_Square.eq.Zero.of.Gt_0.Le_0), Logic.Imp_And.given.Imp.And.subst.apply(Eq[-1])

    Eq << Logic.Imp_And.given.Imp.delete.apply(Eq[-1])

    Eq <<= Logic.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq[-1])

    Eq <<= Eq[-1].this.lhs.apply(Logic.Cond.of.Eq.Cond.subst)

    Eq << Eq[-1].this.lhs.apply(Algebra.Inf_Square.eq.Zero.of.Lt_0, x)





if __name__ == '__main__':
    run()
# created on 2019-12-21
# updated on 2025-04-10
