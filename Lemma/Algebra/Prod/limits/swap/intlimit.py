from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.limits.swap.intlimit import limits_swap
    return Equal(self, limits_swap(Product, self))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    i, j, d, a = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Symbol(shape=(oo,), real=True)
    g = Symbol(shape=(oo, oo), real=True)
    Eq << apply(Product[i:a + d:j + d, j:a:n](f[i] + g[i, j]))

    Eq << Eq[0].this.lhs.apply(Algebra.Prod.eq.Prod_Pow_Bool)

    Eq << Eq[-1].this.find(And).apply(Set.In.In.transform.i_Lt_j.left_close)

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod.eq.Prod_Pow_Bool)

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod.limits.swap)




if __name__ == '__main__':
    run()

# https://en.wikipedia.org/wiki/Iverson_bracket
# created on 2020-03-08
# updated on 2022-01-28
