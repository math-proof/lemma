from util import *


@apply
def apply(m_is_nonnegative, lt_mM, lt, x=None):
    m = m_is_nonnegative.of(Expr >= 0)
    S[m], M = lt_mM.of(Less)

    U, M2 = lt.of(Less)
    _M = M2.of(Expr ** 2)
    assert _M == M or _M == -M
    if x is None:
        x = lt.generate_var(real=True)
    return Any[x:Interval(m, M, left_open=True, right_open=True)](x ** 2 > U)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    m, M, U = Symbol(real=True, given=True)
    Eq << apply(m >= 0, m < M, U < M ** 2)

    x = Eq[-1].variable
    Eq.ge, Eq.lt = Logic.Cond.given.Imp.ImpNot.apply(Eq[-1], cond=U >= m ** 2)

    Eq << Algebra.Gt.of.Lt.Ge.apply(Eq[1], Eq[0])

    Eq << Eq.lt.this.rhs.apply(Algebra.Any.given.Cond.subst, x, (m + M) / 2)

    Eq.gt, Eq.contains = Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq << Eq[1].reversed + m

    Eq << Eq[-1] / 2

    Eq << Algebra.GtSquare.of.Ge_0.Gt.apply(Eq[0], Eq[-1])

    Eq << Logic.Imp.And.of.Cond.apply(Eq[-1], cond=U < m ** 2)

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt.of.Gt.Lt)

    Eq << Logic.Imp.given.Cond.apply(Eq.contains)

    Eq << Set.In.Icc.of.Lt.average.apply(Eq[1])

    Eq << Eq.ge.this.rhs.apply(Algebra.Any.given.Cond.subst, x, (sqrt(U) + M) / 2)

    Eq << Eq[-1].this.find(Element).apply(Set.In_Ico.given.Ge.Lt)

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq[-1], index=None)

    Eq <<= Eq[-1].this.rhs.apply(Algebra.Gt.given.Gt_0), Eq[-3].this.rhs.apply(Algebra.Lt.transport, lhs=0)

    Eq <<= Eq[-2].this.find(Add).apply(Algebra.Sub.Square.eq.Mul), Eq[-1].this.rhs * 2

    Eq <<= Eq[-2].this.lhs.apply(Algebra.Ge.of.Ge.relax, lower=0), Eq[-1].this.lhs.apply(Algebra.Ge.of.Ge.relax, lower=0)

    Eq.is_nonnegative = Eq[-2].this.rhs.apply(Algebra.Mul.gt.Zero.given.And.Gt_0)

    Eq <<= Logic.Imp.And.of.Cond.apply(Eq[2], cond=U >= 0)

    Eq << Eq[-1].this.rhs.apply(Algebra.LtSqrt.of.Ge_0.Lt)

    Eq << Algebra.EqAbs.of.Gt_0.apply(Eq[4])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Logic.Imp_And.given.Imp.Imp.apply(Eq.is_nonnegative)

    Eq <<= Eq[-2].this.rhs * 2, Eq[-1].this.rhs * 2

    Eq <<= Eq[-2].this.rhs.apply(Algebra.Add.gt.Zero.given.And, 0), Eq[-1].this.rhs.apply(Algebra.Gt_0.given.Gt)

    Eq <<= Eq[-2].this.rhs.args[1] / 3, Eq[-1].this.rhs.reversed

    Eq <<= Logic.Imp_And.given.Imp.Imp.apply(Eq[-1])

    Eq <<= Logic.Imp.given.Cond.apply(Eq[-2])

    Eq <<= Eq[-1].this.lhs.apply(Algebra.GeSqrt_0.of.Ge_0)

    Eq << Logic.Imp.And.of.Cond.apply(Eq[1].reversed, cond=U >= m ** 2)

    Eq << Eq[-1].this.rhs.args[1].apply(Algebra.GeSqrt.of.Ge)

    Eq << Algebra.EqAbs.of.Ge_0.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.GtAdd.of.Gt.Ge)

    Eq << Eq[-1].this.rhs / 2





if __name__ == '__main__':
    run()
# created on 2019-07-07
# updated on 2023-05-20
