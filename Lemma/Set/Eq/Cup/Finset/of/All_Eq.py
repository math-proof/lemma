from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(All[Equal])

    return Equal(Cup(FiniteSet(lhs), *limits).simplify(), Cup(FiniteSet(rhs), *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Set
    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    f, g = Symbol(shape=(oo,), etype=dtype.integer)

    Eq << apply(All[i:n](Equal(f[i], g[i])))

    Eq << Eq[0].this.expr.apply(Set.Eq.of.Eq.set, simplify=False)

    Eq << Set.EqCupS.of.All_Eq.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-07-23
