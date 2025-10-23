from util import *


@apply
def apply(self):
    fij, (j, S[0], n), (i, S[0], S[n]) = self.of(Sum)

    sum_eq = Sum[i:n](fij._subs(j, i))
    sum_lt = Sum[j:i, i:n](fij)
    sum_gt = Sum[i:j, j:n](fij)
    return Equal(self, sum_eq + sum_lt + sum_gt, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset, Finset, Finset

    x = Symbol(real=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Sum[j:n, i:n](x[i, j]))

    Eq << Eq[0].this.lhs.apply(Algebra.Sum.eq.Add.split.limits)

    Eq << Eq[-1].this.lhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.limits.swap.subst)


if __name__ == '__main__':
    run()
# created on 2023-05-02
