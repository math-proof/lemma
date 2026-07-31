from util import *


@apply
def apply(self):
    x = self.of(coth)
    return Equal(self, cosh(x) / sinh(x))


@prove
def prove(Eq):
    from Lemma import Real

    x = Symbol(real=True)
    Eq << apply(coth(x))

    Eq << Eq[0].this.lhs.apply(Real.Coth.eq.Inv.Tanh)

    Eq << Eq[-1].this.find(tanh).apply(Real.Tanh.eq.Div)


if __name__ == '__main__':
    run()
# created on 2023-11-26
del Add
from . import Add
