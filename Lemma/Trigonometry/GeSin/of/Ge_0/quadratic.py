from util import *


@apply
def apply(ge_zero):
    x = ge_zero.of(Expr >= 0)
    return sin(x) >= x * (1 - x / S.Pi)

@prove
def prove(Eq):
    from Lemma import Algebra, Trigonometry, Set, Logic

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << Logic.Cond.given.Imp.ImpNot.apply(Eq[1], cond=x > S.Pi)

    Eq << (x <= 0).this.apply(Trigonometry.GeSin.of.Le_0.quadratic)

    Eq << Eq[-1].subs(x, S.Pi - x)

    Eq << Eq[-1].this.lhs.apply(Algebra.Le_0.given.Ge)

    Eq << Eq[-1].find(Mul).this.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Add ** 2).apply(Algebra.Pow.eq.Add)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq.eq_identity = Eq[-1].this.rhs.apply(Algebra.AddMulS.eq.Mul_Add)

    Eq << Eq[-4].subs(Eq.eq_identity)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ge.given.Gt)

    Eq << Logic.Imp.given.And.Imp.split.apply(Eq[3], cond=x > S.Pi / 2)

    Eq << Logic.Imp.given.And.Imp.invert.apply(Eq[-1], cond=x >= 0)

    Eq << Eq[-1].this.lhs.apply(Set.In_Icc.of.Le.Ge)

    Eq << Eq[-1].this.lhs.apply(Trigonometry.GeSin.of.In_Icc.quadratic)

    Eq << Eq[-1].subs(x, S.Pi - x)

    Eq << Eq[-1].subs(Eq.eq_identity)

    Eq << Eq[-1].this.lhs.apply(Set.In_Icc.Is.InNeg)

    Eq << Eq[-1].this.lhs.apply(Set.In_Icc.Is.InAdd, S.Pi)

    Eq << Eq[-1].this.lhs.apply(Set.In_Icc.Is.And)

    Eq << Eq[-1].this.find(And[~GreaterEqual]).apply(Algebra.Ge.given.Gt)




if __name__ == '__main__':
    run()
# created on 2023-10-03
