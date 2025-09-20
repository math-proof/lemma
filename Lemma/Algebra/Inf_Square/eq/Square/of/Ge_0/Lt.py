from util import *


@apply
def apply(is_nonnegative, lt, left_open=True, right_open=True, x=None):
    m = is_nonnegative.of(Expr >= 0)
    S[m], M = lt.of(Less)
    if x is None:
        x = lt.generate_var(real=True)

    self = Inf[x:Interval(m, M, left_open=left_open, right_open=right_open)](x ** 2)
    return Equal(self, m ** 2)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    m, M = Symbol(real=True, given=True)
    x = Symbol(real=True)
    Eq << apply(m >= 0, m < M, x=x)

    Eq << Set.In.Icc.of.Lt.average.apply(Eq[1])

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[-1])

    Eq << Algebra.Gt.of.Gt.Ge.apply(Eq[-2], Eq[0])

    Eq.eq_max = Algebra.EqMax.of.Ge_0.Lt.apply(Eq[0], Eq[1])

    Eq << Algebra.Gt.of.Ge.Lt.apply(Eq[0], Eq[1])

    Eq.eq_abs_M = Algebra.EqAbs.of.Gt_0.apply(Eq[-1])

    Eq.eq_abs_m = Algebra.EqAbs.of.Ge_0.apply(Eq[0])

    Eq << Algebra.Eq.given.And.squeeze.apply(Eq[2])

    y = Symbol(real=True)
    Eq <<= Algebra.LeInf.given.All_Any_Lt.apply(Eq[-2], y), Algebra.GeInf.given.All.Ge.apply(Eq[-1])

    Eq <<= Algebra.All.given.And.All.split.apply(Eq[-2], cond=y <= M ** 2), Logic.All.given.Imp.apply(Eq[-1])

    Eq <<= Logic.All.given.Imp.apply(Eq[-3]), Eq[-2].subs(Eq.eq_max), Eq[-1].this.lhs.apply(Set.Gt.of.In_Icc)

    Eq <<= Eq[-3].this.rhs.apply(Algebra.Any.given.Cond.subst, x, (m + sqrt(y)) / 2), Eq[-2].this.expr.apply(Algebra.Any.given.Cond.subst, x, (M + m) / 2), Eq[-1].this.lhs.apply(Logic.Imp.And.of.Cond, cond=Eq[0])

    Eq <<= Logic.Imp_And.given.Imp.Imp.apply(Eq[-3]), Logic.And_And.given.And.Cond.apply(Eq[-2]), Logic.Imp_Imp.given.And.Imp.apply(Eq[-1])

    Eq << Algebra.Cond.given.Cond.subst.Bool.apply(Eq[-2], cond=Eq[0], invert=True)

    Eq <<= Eq[-5].this.lhs.apply(Set.Gt.of.In_Icc), Eq[-4].this.rhs.apply(Set.In.given.In.Sub, m / 2), Eq[-3].this.expr.apply(Algebra.Lt.given.Gt_0), Eq[-1].this.lhs.apply(Algebra.GtSquare.of.Ge_0.Gt)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge.of.Gt.relax)

    Eq <<= Eq[-4].this.rhs.apply(Algebra.Lt.given.Gt_0), Eq[-3].this.rhs.apply(Set.In.given.In.Mul.Icc, 2), Logic.All.given.Imp.apply(Eq[-2])

    Eq <<= Eq[-3].this.rhs.lhs.apply(Algebra.Sub.Square.eq.Mul), Eq[-2].this.lhs.apply(Set.In.Sqrt.of.In), Eq[-1].this.rhs.lhs.apply(Algebra.Sub.Square.eq.Mul)

    Eq <<= Eq[-3].this.rhs.apply(Algebra.Mul.gt.Zero.given.And.Gt_0), Eq[-2].subs(Eq.eq_abs_m, Eq.eq_abs_M), Eq[-1].this.rhs.apply(Algebra.Mul.gt.Zero.given.And.Gt_0)

    Eq <<= Logic.Imp_And.given.Imp.Imp.apply(Eq[-3]), Eq[-2].this.rhs.apply(Set.In.given.And.strengthen, M, strict=True), Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-4].this.rhs * 2, Eq[-5].this.rhs * 2, Logic.Imp.given.Cond.apply(Eq[-3]), Eq[-1].this.lhs.apply(Algebra.GtSqrt.of.Gt), Eq[-2].this.rhs.apply(Algebra.Add.gt.Zero.given.And.Gt_0, 1)

    Eq << Eq[-3] + (m - M)

    Eq <<= Eq[-5].this.lhs.apply(Algebra.GtSqrt.of.Gt), Eq[-4].this.rhs.apply(Algebra.Add.gt.Zero.given.And), Eq[-2].subs(Eq.eq_abs_M), Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Eq[-5].subs(Eq.eq_abs_m), Eq[-4].this.lhs.apply(Algebra.Gt.of.Gt.relax, lower=0), Eq[-3].this.rhs.apply(Algebra.Gt.transport, lhs=slice(1, None)), Logic.Imp.given.Cond.apply(Eq[-2]), Eq[-1].this.lhs.apply(Algebra.Gt.of.Gt.relax, lower=0)

    Eq << Eq[-4].this.lhs.apply(Algebra.Gt_0.of.Gt)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.Sqrt.of.Gt_0)

    Eq <<= Logic.Imp_And.given.Imp.Imp.apply(Eq[-3]), Eq[-2].this.rhs.apply(Algebra.Gt.given.And.strengthen, M, strict=True)

    Eq <<= Logic.Imp.given.Cond.apply(Eq[-2]), Eq[-3].this.rhs / 3, Eq[-1].this.lhs.apply(Algebra.Ge.of.Gt.relax)

    Eq << Logic.Imp.given.Cond.apply(Eq[-1])

    Eq << Eq[-1] * 2 - M

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2019-07-02
# updated on 2023-05-20
