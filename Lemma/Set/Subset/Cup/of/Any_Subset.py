from util import *


@apply
def apply(given):
    (lhs, rhs), *limits = given.of(Any[Subset])
    variables = [v for v, *_ in limits]
    assert not lhs.has(*variables)
    return Subset(lhs, Cup(rhs, *limits).simplify())


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    g = Function(shape=(), etype=dtype.integer)
    A = Symbol(etype=dtype.integer)
    Eq << apply(Any[i:n](Subset(A, g(i))))

    Eq << All[i:n](Subset(g(i), Cup[i:n](g(i))), plausible=True)

    Eq << Eq[-1].this.find(Cup).apply(Set.Cup.eq.UnionCupS, cond={i})

    Eq << Eq[-1].this.expr.apply(Set.Subset_union.given.Supset, 0)

    Eq << Eq[-1].this().find(Intersection).simplify()

    Eq << Eq[2].this.expr.apply(Set.EqUnion.of.Subset)

    Eq << Eq[0].this.expr.apply(Set.Subset.Union.of.Subset.rhs, Eq[1].find(Cup))

    Eq << Bool.Any_And.of.Any.All.All_Imp.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.expr.apply(Bool.Cond.of.Eq.Cond.subst)


if __name__ == '__main__':
    run()
# created on 2023-06-01
