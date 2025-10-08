from util import *


@apply
def apply(is_negative, lt, fx, x=None, left_open=True, right_open=True):
    from Lemma.Algebra.Le.of.Le.Ge.quadratic import quadratic_coefficient
    m, M = lt.of(Less)
    a = is_negative.of(Expr < 0)

    x, S[a], b, c = quadratic_coefficient(fx, x=x)

    y0 = a * m ** 2 + b * m + c
    y1 = a * M ** 2 + b * M + c
    interval = Interval(m, M, left_open=left_open, right_open=right_open)
    return Equal(Sup[x:interval](fx),
                 Piecewise((c - b ** 2 / (4 * a), Element(-b / (2 * a), interval)),
                           (Max(y0, y1), True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    m, M, x, a, b, c = Symbol(real=True, given=True)
    Eq << apply(a < 0, m < M, a * x ** 2 + b * x + c, x)

    Eq << Algebra.Div.lt.Zero.of.Lt_0.apply(Eq[0])

    Eq << Eq[2].this.lhs.apply(Algebra.Sup.eq.Add)

    Eq << Eq[-1].this.find(Max).apply(Algebra.Max.eq.Add)

    Eq << Eq[-1].this.rhs.apply(Algebra.Ite.eq.SubIte)

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=Eq[-1].find(Element))

    Eq <<= Bool.Imp.given.Imp.subst.Bool.apply(Eq[-2]), Bool.Imp.given.Imp.subst.Bool.apply(Eq[-1], invert=True)

    Eq <<= Bool.Cond.Imp.given.And.Imp.And.apply(Eq[0], Eq[-2]), Eq[-1].this.lhs.apply(Set.Or.of.NotIn_Icc)

    Eq <<= Eq[-2].this.lhs.apply(Set.SupAddMul_Square.eq.Sub.of.Lt_0.In, Eq[-2].find(Sup).expr, x), Bool.ImpOr.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-2].this.find(Sup).apply(Algebra.Sup.limits.subst.offset, Eq[3].lhs * -b /2), Eq[-1].this.find(Sup).apply(Algebra.Sup.limits.subst.offset, Eq[3].lhs * -b /2)

    Eq <<= Eq[-2].this.find(Sup).expr.expand(), Eq[-1].this.find(Sup).expr.expand()

    Eq <<= Eq[-2].this.find(Equal).apply(Algebra.EqAdd.Is.Eq_Sub, lhs=0), Eq[-1].this.find(Equal).apply(Algebra.EqAdd.Is.Eq_Sub, lhs=0)

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Ge_0.of.Le), Eq[-1].this.lhs.apply(Algebra.Le_0.of.Ge)

    Eq <<= Eq[-2].this.rhs.rhs.apply(Algebra.Add.eq.Max), Eq[-1].this.rhs.rhs.apply(Algebra.Add.eq.Max)

    Eq << Eq[1] + Eq[3].lhs * b /2

    Eq <<= Bool.Imp_And.of.Cond.apply(Eq[-1] & Eq[0], cond=Eq[-1].lhs >= 0), Bool.Imp_And.of.Cond.apply(Eq[-1] & Eq[0], cond=Eq[-1].rhs <= 0)

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Sup_Square.eq.Square.of.Lt_0.Ge_0.Lt), \
        Eq[-2].this.rhs.apply(Algebra.Max.eq.Square.of.Lt_0.Ge_0.Lt),\
        Eq[-1].this.rhs.apply(Algebra.Sup_Square.eq.Square.of.Lt_0.Le_0.Lt),\
        Eq[-1].this.rhs.apply(Algebra.Max.eq.Square.of.Lt_0.Le_0.Lt)

    Eq <<= Eq[-4] & Eq[-3], Eq[-2] & Eq[-1]

    Eq <<= Eq[-2].this.rhs.apply(Bool.Eq.of.Eq.Eq, reverse=True), Eq[-1].this.rhs.apply(Bool.Eq.of.Eq.Eq, reverse=True)

    Eq <<= Eq[-2].this.rhs.rhs.expand(), Eq[-1].this.rhs.rhs.expand()




if __name__ == '__main__':
    run()
# created on 2019-12-26
# updated on 2021-10-02
