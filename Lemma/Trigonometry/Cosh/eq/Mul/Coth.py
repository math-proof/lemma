from util import *


@apply
def apply(self):
    x = self.of(cosh)
    return Equal(self, coth(x) * sinh(x))


@prove
def prove(Eq):
    from Lemma import Trigonometry

    x = Symbol(real=True)
    Eq << apply(cosh(x))

    Eq << Eq[0].this.find(coth).apply(Trigonometry.Coth.eq.Div)


if __name__ == '__main__':
    run()
# created on 2023-11-26
