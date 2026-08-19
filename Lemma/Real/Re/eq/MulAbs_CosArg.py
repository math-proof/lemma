from util import *


@apply
def apply(self):
    z = self.of(Re)

    return Equal(self, abs(z) * cos(Arg(z)))


@prove
def prove(Eq):
    from Lemma import Nat, Real, Complex

    z = Symbol(complex=True, given=True)
    Eq << apply(Re(z))

    Eq << Eq[0].this.find(cos).apply(Real.Cos.Arg.eq.Ite)

    Eq << Eq[-1].this.rhs.apply(Nat.Mul_Ite.eq.Ite_MulS)

    Eq << Eq[-1].this.find(Abs).apply(Complex.Norm.eq.Sqrt)




if __name__ == '__main__':
    run()
# created on 2018-06-13
# updated on 2022-01-23
