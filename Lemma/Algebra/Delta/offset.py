from util import *


@apply
def apply(self, offset):
    x, y = self.of(KroneckerDelta)
    return Equal(self, KroneckerDelta(x + offset, y + offset))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, t, a = Symbol(integer=True)
    Eq << apply(KroneckerDelta(x - t, y), t)

    Eq << Eq[0].this.lhs.apply(Algebra.Delta.Sub)

    Eq << Eq[-1].this.rhs.apply(Algebra.Delta.Sub, reverse=True)




if __name__ == '__main__':
    run()
# created on 2021-12-29
