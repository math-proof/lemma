from util import *


@apply
def apply(self):
    z = self.of(Im)

    return Equal(self, abs(z) * sin(Arg(z)))


@prove
def prove(Eq):
    from Lemma import Nat, Complex

    z = Symbol(complex=True, given=True)
    Eq << apply(Im(z))

    Eq << Eq[0].this.find(sin).apply(Complex.SinArg.eq.DivIm_SqrtAddSquareS)

    Eq << Eq[-1].this.rhs.apply(Nat.Mul_Ite.eq.Ite_MulS)

    Eq << Eq[-1].this.find(Abs).apply(Complex.Norm.eq.Sqrt)




if __name__ == '__main__':
    run()
# created on 2018-07-25
# updated on 2022-01-23
