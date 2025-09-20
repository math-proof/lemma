from util import *


@apply
def apply(self):
    z = self.of(Cos[Arg])
    x = Re(z)
    y = Im(z)
    r = sqrt(x ** 2 + y ** 2)
    return Equal(self, Piecewise((1, Equal(z, 0)), (x / r, True)))


@prove
def prove(Eq):
    from Lemma import Algebra, Trigonometry

    z = Symbol(complex=True, given=True)
    Eq << apply(cos(Arg(z)))

    Eq << Algebra.Expr.eq.AddRe_MulIIm.apply(z)

    Eq << Algebra.EqArg.of.Eq.apply(Eq[1])

    Eq << Eq[-1].this.rhs.apply(Trigonometry.Arg.eq.Ite.Arccos)

    Eq << Trigonometry.EqCos.of.Eq.apply(Eq[-1])

    Eq << Eq[0].this.find(Equal).apply(Algebra.Eq_0.Is.And.Eq_0)


if __name__ == '__main__':
    run()
# created on 2018-06-12
