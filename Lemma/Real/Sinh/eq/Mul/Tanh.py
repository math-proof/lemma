from util import *


@apply
def apply(self):
    x = self.of(sinh)
    return Equal(self, tanh(x) * cosh(x))


@prove
def prove(Eq):
    from Lemma import Real

    x = Symbol(real=True)
    Eq << apply(sinh(x))

    Eq << Eq[0].this.find(tanh).apply(Real.Tanh.eq.Div)


if __name__ == '__main__':
    run()
# created on 2023-11-26
