from util import *


@apply
def apply(self):
    x = self.of(-Ceil)
    return Equal(self, floor(-x))


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True)
    Eq << apply(-ceil(x))

    Eq << Eq[0].this.rhs.apply(Algebra.Floor.eq.Neg.Ceil)


if __name__ == '__main__':
    run()
# created on 2020-01-29
