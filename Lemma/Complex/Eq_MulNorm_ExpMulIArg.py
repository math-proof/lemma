from util import *


@apply
def apply(self):
    return Equal(self, abs(self) * exp(S.ImaginaryUnit * Arg(self)))


@prove
def prove(Eq):
    from Lemma import Algebra, Complex, Real, Nat

    z = Symbol(complex=True, given=True)
    Eq << apply(z)

    Eq << Eq[0].this.find(Exp).apply(Real.ExpMulI.eq.AddCos_MulISin.Euler)

    Eq << Eq[-1].this.lhs.apply(Complex.Expr.eq.AddRe_MulIIm)

    Eq << Eq[-1].this.rhs.apply(Nat.Mul_Add.eq.AddMulS)

    Eq << Algebra.Eq.given.And.Eq.complex.apply(Eq[-1])

    Eq << Eq[-2].this.lhs.apply(Complex.Re.eq.MulNorm_CosArg)
    Eq << Eq[-1].this.lhs.apply(Complex.Im.eq.MulNorm_SinArg)


if __name__ == '__main__':
    run()
# created on 2018-07-26
