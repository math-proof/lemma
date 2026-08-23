from util import *


@apply
def apply(gt_zero, lt, fx, x=None, left_open=True, right_open=True):
    from Lemma.Real.Le.of.Le.Ge.quadratic import quadratic_coefficient
    m, M = lt.of(Less)
    a = gt_zero.of(Expr > 0)

    x, S[a], b, c = quadratic_coefficient(fx, x=x)

    y0 = a * m ** 2 + b * m + c
    y1 = a * M ** 2 + b * M + c
    interval = Interval(m, M, left_open=left_open, right_open=right_open)
    return Equal(Inf[x:interval](fx),
                 Piecewise((c - b ** 2 / (4 * a), Element(-b / (2 * a), interval)),
                           (Min(y0, y1), True)))


@prove
def prove(Eq):
    from Lemma import Set, Bool, Int, Nat, Rat, Real

    m, M, x, a, b, c = Symbol(real=True, given=True)
    Eq << apply(a > 0, m < M, a * x ** 2 + b * x + c, x)

    Eq << Rat.Lt0Div.of.Gt_0.apply(Eq[0])

    Eq << Eq[2].this.lhs.apply(Real.Inf.eq.Add)

    Eq << Eq[-1].this.find(Min).apply(Nat.Min.eq.Add)

    Eq << Eq[-1].this.rhs.apply(Nat.Ite.eq.SubIte)

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=Eq[-1].find(Element))

    Eq <<= Bool.Imp_Ite.given.Imp.apply(Eq[-2]), Bool.Imp_Ite.given.Imp.apply(Eq[-1], invert=True)

    Eq <<= Bool.And_Imp.given.And_ImpAnd.apply(Eq[0], Eq[-2]), Eq[-1].this.lhs.apply(Set.Or.of.NotIn_Icc)

    Eq <<= Eq[-2].this.lhs.apply(Set.Inf_Add_Mul_Square.eq.Sub_DivSquare.of.Gt_0.In, Eq[-2].find(Inf).expr, x), Bool.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-2].this.find(Inf).apply(Real.Inf.limits.subst.offset, Eq[3].lhs * -b /2), Eq[-1].this.find(Inf).apply(Real.Inf.limits.subst.offset, Eq[3].lhs * -b /2)

    Eq <<= Eq[-2].this.find(Inf).expr.expand(), Eq[-1].this.find(Inf).expr.expand()

    Eq <<= Eq[-2].this.find(Equal).apply(Int.EqAdd.Is.Eq_Sub, lhs=0), Eq[-1].this.find(Equal).apply(Int.EqAdd.Is.Eq_Sub, lhs=0)

    Eq <<= Eq[-2].this.lhs.apply(Nat.Ge_0.of.Le), Eq[-1].this.lhs.apply(Nat.Le_0.of.Ge)

    Eq <<= Eq[-2].this.rhs.rhs.apply(Nat.Add.eq.Min), Eq[-1].this.rhs.rhs.apply(Nat.Add.eq.Min)

    Eq << Eq[1] + Eq[3].lhs * b /2

    Eq <<= Bool.Imp_And.of.Cond.apply(Eq[-1] & Eq[0], cond=Eq[-1].lhs >= 0), Bool.Imp_And.of.Cond.apply(Eq[-1] & Eq[0], cond=Eq[-1].rhs <= 0)

    Eq <<= Eq[-2].this.rhs.apply(Real.Inf_Square.eq.Square.of.Gt_0.Ge_0.Lt), \
        Eq[-2].this.rhs.apply(Nat.Min.eq.Square.of.Gt_0.Ge_0.Lt),\
        Eq[-1].this.rhs.apply(Real.Inf_Square.eq.Square.of.Gt_0.Le_0.Lt),\
        Eq[-1].this.rhs.apply(Int.Min.eq.Square.of.Gt_0.Le_0.Lt)

    Eq <<= Eq[-4] & Eq[-3], Eq[-2] & Eq[-1]

    Eq <<= Eq[-2].this.rhs.apply(Bool.Eq.of.Eq.Eq, reverse=True), Eq[-1].this.rhs.apply(Bool.Eq.of.Eq.Eq, reverse=True)

    Eq <<= Eq[-2].this.rhs.rhs.expand(), Eq[-1].this.rhs.rhs.expand()




if __name__ == '__main__':
    run()
# created on 2021-10-02
# updated on 2023-05-20
