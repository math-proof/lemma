from util import *


@apply
def apply(self):
    assert self.is_KroneckerDelta
    return Element(self, {0, 1})


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    x, y = Symbol(real=True)
    Eq << apply(KroneckerDelta(x, y))

    Eq << Eq[-1].this.lhs.apply(Algebra.Delta.eq.Ite)

    Eq << Set.Bool.In.Finset.apply(Equal(x, y).toNat)

    Eq << Eq[-1].this.lhs.apply(Bool.Bool.eq.Ite)


if __name__ == '__main__':
    run()

# created on 2021-04-22
