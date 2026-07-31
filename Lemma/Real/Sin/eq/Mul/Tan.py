from util import *


@apply
def apply(self):
    x = self.of(sin)
    return Equal(self, tan(x) * cos(x))


@prove
def prove(Eq):
    from Lemma import Real

    x = Symbol(real=True)
    Eq << apply(sin(x))

    Eq << Eq[0].this.find(tan).apply(Real.Tan.eq.Div)


if __name__ == '__main__':
    run()
# created on 2023-11-26
