from util import *


@apply
def apply(is_positive, lt, fx, x=None, left_open=True, right_open=True):
    from Lemma.Algebra.Le.of.Le.Ge.quadratic import quadratic_coefficient
    m, M = lt.of(Less)
    a = is_positive.of(Expr > 0)

    x, S[a], b, c = quadratic_coefficient(fx, x=x)

    y0 = a * m ** 2 + b * m + c
    y1 = a * M ** 2 + b * M + c

    return Equal(Sup[x:Interval(m, M, left_open=left_open, right_open=right_open)](fx), Max(y0, y1))


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    m, M, x, a, b, c = Symbol(real=True, given=True)
    Eq << apply(a > 0, m < M, a * x ** 2 + b * x + c, x)

    Eq.a_reciprocal = Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(Algebra.Sup.limits.subst.offset, -b * Eq.a_reciprocal.lhs / 2)

    Eq << Eq[-1].this.rhs.apply(Algebra.Max.eq.Add)

    Eq.eq = Eq[-1].this.lhs.expr.expand()

    Eq << Eq[1] + Eq.a_reciprocal.lhs * b / 2

    Eq << Algebra.Sup_Square.eq.Max.of.Lt.apply(Eq[-1])

    Eq << Algebra.Mul.eq.Sup.of.Gt_0.apply(Eq[0], Eq[-1].lhs)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq.eq.subs(Eq[-1].reversed)

    Eq << Algebra.Ne.of.Gt.apply(Eq[0])

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-2])

    Eq << Algebra.Mul.eq.Max.of.Gt_0.apply(Eq[0], Eq[-1].lhs.find(Max))

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.eq.Max)

    Eq << Eq[-1].this.find(Add ** 2).apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)

    Eq << Eq[-1].this.find(Add ** 2).apply(Algebra.SquareAdd.eq.AddAddSquareS_MulMul2)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)





if __name__ == '__main__':
    run()
# created on 2019-09-09
# updated on 2025-04-20
