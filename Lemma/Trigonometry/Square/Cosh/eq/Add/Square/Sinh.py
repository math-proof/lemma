from util import *


@apply
def apply(self):
    x = self.of(cosh ** 2)
    return Equal(self, sinh(x) ** 2 + 1)


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(cosh(x) ** 2)

    Eq << Eq[0].this.find(sinh ** 2).apply(Trigonometry.Square.Sinh.eq.Sub.Square.Cosh)


if __name__ == '__main__':
    run()
# created on 2023-11-26
