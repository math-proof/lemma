from util import *


@apply
def apply(self):
    from Lemma.Algebra.AddSumS.eq.Sum_Add_Sum import piece_together
    return Equal(self, piece_together(Minima, self))


@prove
def prove(Eq):
    from Lemma import Algebra

    k, i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f, g = Function(integer=True)
    Eq << apply(Min(Minima[i:k, k:n](f(k, i)), Minima[j:k, k:n](g(k, j))))

    Eq << Eq[-1].this.rhs.apply(Algebra.Minima.eq.Min)




if __name__ == '__main__':
    run()
# created on 2023-04-23
