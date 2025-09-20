from util import *


@apply
def apply(self):
    x = self.of(Sin)
    return Equal(self, Im(E ** (S.ImaginaryUnit * x), evaluate=False))


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(sin(x))

    Eq << Eq[0].this.find(Exp).apply(Trigonometry.ExpMulI.eq.AddCos_MulISin.Euler)


if __name__ == '__main__':
    run()
# created on 2023-06-03
