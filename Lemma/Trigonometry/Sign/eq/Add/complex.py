from util import *


@apply
def apply(self):
    x = self.of(Sign)
    assert x.is_nonzero
    return Equal(self, cos(Arg(x)) + S.ImaginaryUnit * sin(Arg(x)))


@prove
def prove(Eq):
    from Lemma import Algebra, Trigonometry

    z = Symbol(complex=True, zero=False)
    Eq << apply(Sign(z))

    Eq << Eq[-1].this.lhs.apply(Algebra.Sign.eq.ExpI.Arg)

    Eq << Eq[-1].this.lhs.apply(Trigonometry.ExpMulI.eq.AddCos_MulISin.Euler)




if __name__ == '__main__':
    run()
# created on 2023-05-25
