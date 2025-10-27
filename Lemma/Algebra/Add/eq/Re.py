from util import *


@apply
def apply(self):
    args = self.of(Add)
    reals = []
    for arg in args:
        if r := arg.of(Re):
            reals.append(r)
        elif r := arg.of(Expr * Re):
            coeff, r = r
            assert coeff.is_super_real
            reals.append(coeff * r)
        else:
            return

    return Equal(self, Re(Add(*reals), evaluate=False))


@prove
def prove(Eq):
    from Lemma import Algebra, Complex

    z, w = Symbol(complex=True)
    Eq << apply(Re(z) + Re(w))

    Eq << Complex.Expr.eq.AddRe_MulIIm.apply(w)

    Eq << Complex.Expr.eq.AddRe_MulIIm.apply(z)

    Eq << Eq[0].subs(*Eq[-2:])




if __name__ == '__main__':
    run()
# created on 2023-06-03
# updated on 2023-06-24
