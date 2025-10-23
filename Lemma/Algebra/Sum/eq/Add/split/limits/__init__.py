from util import *


@apply
def apply(self):
    fij, (j, S[0], n), (i, S[0], S[n]) = self.of(Sum)

    k = Dummy('k', integer=True)
    fji = fij._subs(i, k)._subs(j, i)._subs(k, j)
    sum_eq = Sum[i:n](fij._subs(j, i))
    sum_ne = Sum[j:i, i:n](fij + fji)
    return Equal(self, sum_eq + sum_ne, evaluate=False)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Finset

    x = Symbol(complex=True, shape=(oo, oo))
    i, j = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(Sum[j:n, i:n](x[i, j]))



    Eq << Eq[0].subs(n, n + 1)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.find(Sum[2]).apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.find(Sum[~Sum]).apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.find(Sum[Add]).apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.rhs.args[0].apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.lhs.args[1].apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.rhs.apply(Algebra.Sum.eq.Add.pop)

    Eq << Eq[-1].this.rhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Imply(Eq[0], Eq[1], plausible=True)

    Eq << Bool.Cond.of.All_Imp.apply(Eq[-1], n, 0)





if __name__ == '__main__':
    run()
# created on 2023-04-19
# updated on 2023-05-25

from . import triple
