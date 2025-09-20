from util import *


@apply
def apply(self):
    x = self.of(Ceil)

    return Equal(self, frac(-x) + x)


@prove
def prove(Eq):
    from Lemma import Algebra
    x = Symbol(real=True)
    Eq << apply(ceil(x))

    Eq << Eq[0].this.rhs.args[1].apply(Algebra.Frac.eq.Sub_Floor)

    Eq << Eq[-1].this.lhs.apply(Algebra.Ceil.eq.Neg.Floor)


if __name__ == '__main__':
    run()
# created on 2019-03-06
