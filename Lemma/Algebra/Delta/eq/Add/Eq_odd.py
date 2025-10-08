from util import *


@apply
def apply(self):
    n = self.of(KroneckerDelta[1, Expr % 2])
    return Equal(self, (1 - (-1) ** n) / 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    n = Symbol(integer=True)
    Eq << apply(KroneckerDelta(1, n % 2))

    Eq << Eq[0].this.find(Pow).apply(Algebra.Pow.eq.Ite.negativeOne)

    Eq << Eq[-1].this.find(Mul[Piecewise]).apply(Algebra.Mul.eq.Ite, simplify=None)

    Eq << Eq[-1].this.rhs.apply(Algebra.Add_Ite.eq.Ite_AddS)

    Eq << Eq[-1].this.rhs.apply(Bool.Ite__Ite.eq.IteAnd_Not__Ite)

    Eq << Eq[-1].this.find(Unequal).apply(Algebra.Ne_0.Is.Eq_odd)

    Eq << Eq[-1].this.lhs.apply(Algebra.Delta.eq.Ite, swap=True)


if __name__ == '__main__':
    run()
# created on 2023-05-22
# updated on 2023-05-23
