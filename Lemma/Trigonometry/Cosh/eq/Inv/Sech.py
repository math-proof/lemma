from util import *


@apply
def apply(self):
    x = self.of(cosh)
    return Equal(self, 1 / sech(x))


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(cosh(x))

    Eq << Eq[0].this.find(sech).apply(Trigonometry.Sech.eq.Inv.Cosh)




if __name__ == '__main__':
    run()
# created on 2023-11-26
