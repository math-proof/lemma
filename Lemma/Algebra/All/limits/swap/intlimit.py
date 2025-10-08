from util import *


@apply
def apply(self):
    from Lemma.Algebra.Sum.limits.swap.intlimit import limits_swap
    return limits_swap(All, self)


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool

    i, j, d, a = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    f = Symbol(shape=(oo,), bool=True)
    g = Symbol(shape=(oo, oo), bool=True)
    Eq << apply(All[i:a + d:j + d, j:a + 1:n](f[i] & g[i, j]))

    Eq << Eq[0].this.lhs.apply(Algebra.All.Is.Or)

    Eq << Eq[-1].this.rhs.apply(Algebra.All.Is.Or)

    Eq << Set.In.In.transform.i_Lt_j.apply(*Or(*Eq[-1].find(Or).args[:-1]).invert().args)

    Eq << Eq[-1].this.apply(Bool.Iff.contraposition).reversed

    Eq << Bool.Iff.Or.of.Iff.apply(Eq[-1], cond=Eq[0].lhs.expr)





if __name__ == '__main__':
    run()
# created on 2022-01-24
# updated on 2023-05-21
