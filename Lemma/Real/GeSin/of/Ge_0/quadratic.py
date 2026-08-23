from util import *


@apply
def apply(ge_zero):
    x = ge_zero.of(Expr >= 0)
    return sin(x) >= x * (1 - x / S.Pi)

@prove
def prove(Eq):
    from Lemma import Set, Bool, Nat, Real, Finset

    x = Symbol(real=True)
    Eq << apply(x >= 0)

    Eq << Bool.Cond.given.Imp.ImpNot.apply(Eq[1], cond=x > S.Pi)

    Eq << (x <= 0).this.apply(Real.GeSin.of.Le_0.quadratic)

    Eq << Eq[-1].subs(x, S.Pi - x)

    Eq << Eq[-1].this.lhs.apply(Nat.Le_0.given.Ge)

    Eq << Eq[-1].find(Mul).this.apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Add ** 2).apply(Finset.PowAdd.eq.Sum_MulMulPowS)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Nat.Mul_Add.eq.AddMulS)

    Eq.eq_identity = Eq[-1].this.rhs.apply(Nat.AddMulS.eq.Mul_Add)

    Eq << Eq[-4].subs(Eq.eq_identity)

    Eq << Eq[-1].this.lhs.apply(Nat.Ge.given.Gt)

    Eq << Bool.Imp.given.ImpAnd.ImpAnd_Not.apply(Eq[3], cond=x > S.Pi / 2)

    Eq << Bool.Imp.given.And.Imp.invert.apply(Eq[-1], cond=x >= 0)

    Eq << Eq[-1].this.lhs.apply(Set.In_Icc.of.Le.Le)

    Eq << Eq[-1].this.lhs.apply(Real.GeSin.of.In_Icc.quadratic)

    Eq << Eq[-1].subs(x, S.Pi - x)

    Eq << Eq[-1].subs(Eq.eq_identity)

    Eq << Eq[-1].this.lhs.apply(Set.In_Icc.Is.InNeg)

    Eq << Eq[-1].this.lhs.apply(Set.In_Icc.Is.InAdd, S.Pi)

    Eq << Eq[-1].this.lhs.apply(Set.In_Icc.Is.And)

    Eq << Eq[-1].this.find(And[~GreaterEqual]).apply(Nat.Ge.given.Gt)




if __name__ == '__main__':
    run()
# created on 2023-10-03
