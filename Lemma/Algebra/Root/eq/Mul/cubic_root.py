from util import *


@apply
def apply(self):
    p = self.of((Expr ** 3) ** (S.One / 3))
    return Equal(self, p * exp(-S.ImaginaryUnit * 2 * S.Pi / 3 * Ceil(3 * Arg(p) / (2 * S.Pi) - S.One / 2)))


@prove
def prove(Eq):
    from Lemma import Real, Nat, Complex

    p = Symbol(complex=True, given=True)
    Eq << apply((p ** 3) ** (S.One / 3))

    Eq << Eq[0].this.lhs.apply(Complex.Pow_Inv.eq.Mul_ExpMulIDivArg)

    Eq << Eq[-1].this.find(Arg).apply(Complex.ArgPow.eq.SubMul_Arg)

    Eq << Eq[-1].this.find(Exp[~Mul]).apply(Nat.Mul_Add.eq.AddMulS)
    Eq << Eq[-1].this.find(Exp).apply(Real.ExpAdd.eq.MulExpS)

    Eq << Eq[-1].this.rhs.apply(Complex.Eq_MulNorm_ExpMulIArg)


if __name__ == '__main__':
    run()
# created on 2020-03-11
