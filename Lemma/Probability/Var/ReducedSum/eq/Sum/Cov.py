from util import *


@apply
def apply(self, i=None, j=None):
    (x, (S[0], n)), [S[x[:n]]] = self.of(Variance[ReducedSum[Sliced]])
    return Equal(self, Sum[j:n, i:n](Covariance(x[i], x[j])))


@prove
def prove(Eq):
    from Lemma import Algebra, Probability

    x = Symbol(real=True, shape=(oo,), random=True)
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    Eq << apply(Variance(ReducedSum(x[:n])), i, j)

    Eq << Eq[0].this.find(ReducedSum).apply(Algebra.ReducedSum.eq.Sum)

    Eq << Eq[-1].this.lhs.apply(Probability.Var.Sum.eq.Sum.Cov)




if __name__ == '__main__':
    run()
# created on 2023-04-19

