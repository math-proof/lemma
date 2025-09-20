from util import *


@apply
def apply(self):
    n = self.of(KroneckerDelta[0, Expr % 2])
    return Equal(self, 1 - KroneckerDelta(1, n % 2))


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True)
    Eq << apply(KroneckerDelta(0, n % 2))

    Eq << Eq[0].this.lhs.apply(Algebra.Delta.eq.Add.Eq_even)

    Eq << Eq[-1].this.find(KroneckerDelta).apply(Algebra.Delta.eq.Add.Eq_odd)


if __name__ == '__main__':
    run()
# created on 2023-05-22
