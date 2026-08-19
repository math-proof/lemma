from util import *


@apply
def apply(self):
    z = self.of(Sin[Arg])
    x = Re(z)
    y = Im(z)
    r = sqrt(x ** 2 + y ** 2)
    return Equal(self, Piecewise((0, Equal(z, 0)), (y / r, True)))


@prove
def prove(Eq):
    from Lemma import Complex, Real

    z = Symbol(complex=True, given=True)
    Eq << apply(sin(Arg(z)))

    Eq << Complex.Expr.eq.AddRe_MulIIm.apply(z)

    Eq << Complex.Arg.of.Eq.apply(Eq[1])

    Eq << Eq[-1].this.rhs.apply(Complex.ArgAdd.eq.Ite_Arcsin_Ite_Sub_Arcsin)

    Eq << Real.Sin.of.Eq.apply(Eq[-1])

    Eq << Eq[0].this.find(Equal).apply(Complex.Eq_0.Is.EqRe_0.EqIm_0)


if __name__ == '__main__':
    run()
# created on 2018-07-25
