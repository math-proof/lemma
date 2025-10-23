from util import *


@apply
def apply(self):
    from Lemma.Finset.AddSumS.eq.Sum_Add_Sum import piece_together
    return Equal(self, piece_together(Inf, self))


@prove
def prove(Eq):
    from Lemma import Algebra

    k, i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Function(integer=True)
    Eq << apply(Min(Inf[i:k, k:n](f(k, i)), Inf[j:k, k:n](g(k, j))))

    Eq << Eq[-1].this.rhs.apply(Algebra.Inf.eq.Min)


if __name__ == '__main__':
    run()
# created on 2023-04-23
