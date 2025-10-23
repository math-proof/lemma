from util import *


@apply
def apply(self, j=None):
    (xi, (i, S[0], n)), *limits_v = self.of(Variance[Sum])
    assert not self.is_random
    assert i != j
    if j is None:
        j = self.generate_var(integer=True, excludes=i)
    xj = xi._subs(i, j)
    assert not xj._has(i)
    return Equal(self, Sum[j:n, i:n](Covariance(xi, xj)))


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Bool, Finset, Finset, Finset

    x = Symbol(real=True, shape=(oo,), random=True)
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(Variance(Sum[i:n](x[i])), j)

    Eq.induct = Eq[0].subs(n, n + 1)

    Eq << Eq.induct.this.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.lhs.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.lhs.apply(Probability.Var.Add.eq.Add.Cov)

    Eq << Eq[-1].this.find(Covariance).apply(Probability.Cov.Sum.eq.Sum.Cov)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.lhs.find(Sum[Covariance]).limits_subs(i, j)

    Eq << Eq[-1].this.find(Variance).apply(Probability.Var.eq.Cov)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.find(Sum[~Sum]).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.find(Covariance).apply(Probability.Cov.Sum.eq.Sum.Cov)

    Eq << Imply(Eq[0], Eq.induct, plausible=True)

    Eq << Bool.Cond.of.All_Imp.apply(Eq[-1], n, 0)




if __name__ == '__main__':
    run()
# created on 2023-04-19

