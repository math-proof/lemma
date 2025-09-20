from util import *


@apply
def apply(ge_zero):
    x = ge_zero.of(Expr >= 0)
    return sin(x) >= x * (S.Pi ** 2 - x ** 2)/(S.Pi ** 2 + x ** 2)

@prove
def prove(Eq):
    from Lemma import Algebra, Set, Trigonometry, Logic

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[1], cond=x > 0)

    Eq << Logic.Imp.given.And.Imp.split.apply(Eq[-1], cond=x >= 0)

    Eq << Logic.Imp.given.Imp.subst.apply(Eq[-2])

    Eq << Logic.Imp.given.Cond.invert.apply(Eq[-1])

    Eq.lt, Eq.ge = Logic.Imp.given.And.Imp.split.apply(Eq[2], cond=x < S.Pi)

    Eq << Eq.lt.this.lhs.apply(Set.In.Icc.of.Lt.Gt)

    Eq << Eq[-1].this.lhs.apply(Trigonometry.GtSin.of.In_Icc)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge.of.Gt.relax)

    Eq << Logic.Imp.given.And.Imp.split.apply(Eq.ge, cond=x > S.Pi)

    Eq << Logic.Imp.given.Imp.subst.apply(Eq[-1])

    t = Symbol(x - S.Pi)
    Eq << t.this.definition

    Eq << Eq[-1] + S.Pi

    Eq << Eq[-4].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.find(Greater).simplify()

    Eq << Eq[-1].this.find(Expr ** 2 - Expr ** 2).apply(Algebra.Sub.Square.eq.Mul)

    Eq.le = -Eq[-1].this.rhs

    Eq.gt_1 = Imply(t > 0, Greater(Mul(*Eq.le.find(Mul).args[1:]), 1), plausible=True)

    Eq << Eq.gt_1.this.rhs * Eq[-1].find((~Expr) ** -1)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS, deep=True)

    Eq << Eq[-1].this.find(Add ** 2).apply(Algebra.Pow.eq.Add)

    Eq << Logic.Imp.given.Imp.And.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Algebra.Gt_0.Gt.given.And.Div)

    Eq << Logic.Imp.And.of.Imp.apply(Eq.gt_1)

    Eq << Eq[-1].this.rhs.apply(Algebra.GtMul.of.Gt_0.Gt)

    Eq << Eq[-1].lhs.this.apply(Trigonometry.LeSin.of.Gt_0)

    Eq <<= Eq[-1] & Eq[-2]

    Eq << Eq[-1].this.rhs.apply(Algebra.Lt.of.Gt.Le)

    Eq << Eq[-1].this.rhs.apply(Algebra.Le.of.Lt)

    # reference:
    # https://www.zhihu.com/question/355479801
    # related paper:
    # https://www.zhihu.com/question/431618787
    # https://www.zhihu.com/question/534567781
    # https://www.zhihu.com/question/471643309



if __name__ == '__main__':
    run()
# created on 2023-10-03
