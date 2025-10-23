from util import *


@apply
def apply(self):
    from Lemma.Finset.AddSumS.eq.Sum_Add_Sum import piece_together
    return Equal(self, piece_together(Sup, self))


@prove
def prove(Eq):
    from Lemma import Algebra

    k, i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Function(integer=True)
    Eq << apply(Max(Sup[i:k, k:n](f(k, i)), Sup[j:k, k:n](g(k, j))))

    Eq << Eq[-1].this.rhs.apply(Algebra.Sup.eq.Max)


if __name__ == '__main__':
    run()
# created on 2023-04-23
