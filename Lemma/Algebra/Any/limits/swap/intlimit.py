from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.limits.swap.intlimit import limits_swap
    return limits_swap(Any, self)


@prove(proved=False)
def prove(Eq):
    from Lemma import Algebra, Set

    i, j, d, a = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Symbol(shape=(oo,), bool=True)
    g = Symbol(shape=(oo, oo), bool=True)
    Eq << apply(Any[i:a + d:j + d, j:a + 1:n](f[i] & g[i, j]))
    return
    Eq << Eq[0].this.lhs.apply(Algebra.All.to.ou)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.to.ou)

    Eq << Set.et_el.transform.i_lt_j.apply(Or(*Eq[-1].find(Or).args[1:]).invert())

    Eq << Eq[-1].this.apply(Algebra.Iff.contraposition).reversed


    Eq << Algebra.Iff.then.Iff.ou.apply(Eq[-1], cond=Eq[0].lhs.expr)


if __name__ == '__main__':
    run()
# created on 2022-01-28
