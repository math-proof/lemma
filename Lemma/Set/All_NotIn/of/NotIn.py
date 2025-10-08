from util import *


@apply
def apply(given):
    e, S = given.of(NotElement)
    expr, *limits = S.of(Cup)
    return All(NotElement(e, expr).simplify(), *limits)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    n = Symbol(integer=True, positive=True)
    x, k = Symbol(integer=True)
    A = Symbol(shape=(oo,), etype=dtype.integer)
    Eq << apply(NotElement(x, Cup[k:n](A[k])))

    k = Symbol(domain=Range(n))
    Eq << Eq[0].this.rhs.apply(Set.Cup.eq.UnionCupS, cond=k.set)

    Eq << Set.AndNotSIn.of.NotIn_Union.apply(Eq[-1], simplify=None)

    Eq << Bool.All.of.Cond.apply(Eq[-2], k)


if __name__ == '__main__':
    run()

# created on 2020-09-09
