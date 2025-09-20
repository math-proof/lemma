from util import *


@apply
def apply(self):
    assert self.is_KroneckerDelta
    return Element(self, {0, 1})


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    x, y = Symbol(real=True)
    Eq << apply(KroneckerDelta(x, y))

    Eq << Eq[-1].this.lhs.apply(Algebra.Delta.eq.Ite)

    Eq << Set.Bool.In.Finset.apply(Bool(Equal(x, y)))

    Eq << Eq[-1].this.lhs.apply(Logic.Bool.eq.Ite)


if __name__ == '__main__':
    run()

# created on 2021-04-22
