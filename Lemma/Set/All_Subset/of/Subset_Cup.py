from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Subset)
    expr, *limits = lhs.of(Cup)
    return All(Subset(expr, rhs).simplify(), *limits)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    x = Symbol(shape=(oo,), etype=dtype.complex[n])
    A = Symbol(etype=dtype.complex[n])
    Eq << apply(Subset(Cup[i:n](x[i]), A))

    k = Symbol(domain=Range(n))
    Eq << Eq[0].this.lhs.apply(Set.Cup.eq.UnionCupS, cond=k.set)

    Eq << Set.Subset.of.Subset.split.Union.apply(Eq[-1])

    Eq << Bool.AllIn.of.All.apply(Eq[-1], (k,))


if __name__ == '__main__':
    run()

# created on 2020-07-28
