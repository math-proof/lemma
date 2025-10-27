from util import *


@apply
def apply(self):
    z = self.of(Abs)
    x = Re(z)
    y = Im(z)
    return Equal(self, sqrt(x * x + y * y))


@prove
def prove(Eq):
    from Lemma import Algebra, Complex
    z = Symbol(complex=True)
    Eq << apply(abs(z))
    Eq << Eq[0].this.lhs.arg.apply(Complex.Expr.eq.AddRe_MulIIm)


if __name__ == '__main__':
    run()

# created on 2018-06-12
