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
    from Lemma import Algebra, Trigonometry, Complex

    z = Symbol(complex=True, given=True)
    Eq << apply(sin(Arg(z)))

    Eq << Complex.Expr.eq.AddRe_MulIIm.apply(z)

    Eq << Algebra.EqArg.of.Eq.apply(Eq[1])

    Eq << Eq[-1].this.rhs.apply(Trigonometry.Arg.eq.Ite.Arcsin)

    Eq << Trigonometry.EqSin.of.Eq.apply(Eq[-1])

    Eq << Eq[0].this.find(Equal).apply(Algebra.Eq_0.Is.And.Eq_0)


if __name__ == '__main__':
    run()
# created on 2018-07-25
