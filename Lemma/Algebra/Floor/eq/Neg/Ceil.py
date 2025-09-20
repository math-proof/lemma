from util import *


@apply
def apply(self):
    x = self.of(Floor)

    return Equal(self, -ceil(-x))


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True)
    Eq << apply(floor(x))

    Eq << -Eq[0]

    Eq << Eq[-1].this.rhs.apply(Algebra.Ceil.eq.Neg.Floor)

if __name__ == '__main__':
    run()

# created on 2018-10-22
