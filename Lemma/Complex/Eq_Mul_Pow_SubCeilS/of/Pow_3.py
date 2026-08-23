from util import *


@apply
def apply(eq_pow):
    A, B = eq_pow.of(Equal)
    from Lemma.Complex.Eq.of.Eq_Pow.Eq_Ceil.cubic_root import cubic_root
    A = cubic_root(A)
    B = cubic_root(B)

    # w = -S.One / 2 + sqrt(3) / 2 * S.ImaginaryUnit
    w = exp(S.ImaginaryUnit * 2 * S.Pi / 3)
    d = Ceil(3 * Arg(A) / (S.Pi * 2) - S.One / 2) - Ceil(3 * Arg(B) / (S.Pi * 2) - S.One/ 2)
    return Equal(A, B * w ** d)


@prove
def prove(Eq):
    from Lemma import Real, Int, Nat, Complex

    A, B = Symbol(complex=True, given=True)
    Eq << apply(Equal(A ** 3, B ** 3))

    d = Symbol(Eq[1].find(Ceil - Ceil))
    Eq << d.this.definition

    Eq.difference = Eq[-1].this.apply(Int.EqAdd.Is.Eq_Sub, rhs=-1).reversed

    Eq << Eq[1].this.lhs.apply(Complex.Eq_MulNorm_ExpMulIArg)

    Eq << Eq[-1].this.rhs.args[0].apply(Complex.Eq_MulNorm_ExpMulIArg)

    Eq << Eq[-1].subs(Eq.difference)

    Eq << Nat.Pow.of.Eq.apply(Eq[0], exp=S.One / 3)

    Eq << Eq[-1].this.lhs.apply(Complex.Pow_Inv.eq.Mul_ExpMulIDivArg)

    Eq << Eq[-1].this.rhs.apply(Complex.Pow_Inv.eq.Mul_ExpMulIDivArg)

    Eq << Eq[-1].this.lhs.find(Arg).apply(Complex.ArgPow.eq.SubMul_Arg)

    Eq << Eq[-1].this.rhs.find(Arg).apply(Complex.ArgPow.eq.SubMul_Arg)

    Eq << Eq[-1].this.lhs.find(Mul[Add]).apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.lhs.find(Exp).apply(Real.ExpAdd.eq.MulExpS)

    Eq << Eq[-1].this.rhs.find(Exp).apply(Real.ExpAdd.eq.MulExpS)

    Eq << Eq[-1].subs(Eq.difference)

    Eq << Eq[-1] / Eq[-1].lhs.args[-1]

    Eq << Eq[-1].this.rhs.args[-1].apply(Complex.Expr.eq.AddRe_MulIIm)


if __name__ == '__main__':
    run()
# created on 2018-08-28
