from util import *


@apply
def apply(self):
    coeff, arg = self.of(Expr * Re)
    assert coeff.is_super_real

    return Equal(self, Re(arg * coeff, evaluate=False))


@prove
def prove(Eq):
    from Lemma import Algebra

    c = Symbol(real=True)
    z = Symbol(complex=True)
    Eq << apply(Re(z) * c)

    Eq << Algebra.Expr.eq.AddRe_MulIIm.apply(z)

    Eq << Eq[0].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2023-06-03
# updated on 2023-06-25
