from util import *


@apply
def apply(given, n=None):
    (xi, xj), (j, i) = given.of(All[Equal[Intersection, EmptySet], Tuple[0, Expr]])

    if not xi.has(i):
        xi, xj = xj, xi

    assert xi.has(i)
    assert xj.has(j)

    return Equal(Card(Cup[i:n](xi)), Sum[i:n](Card(xi)))


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    i, j = Symbol(integer=True)
    n = Symbol(integer=True, positive=True, given=False)
    x = Symbol(shape=(oo,), etype=dtype.integer, finite=True)
    Eq << apply(All[j:i](Equal(x[i] & x[j], x[i].etype.emptySet)), n=n)

    Eq << Eq[0].subs(i, 1)

    Eq << Set.CardUnion.eq.Sub_.AddCards.CardInter.principle.inclusion_exclusion.apply(*Eq[-1].lhs.args).subs(Eq[-1])

    Eq.induct = Eq[1].subs(n, n + 1)

    Eq << Eq.induct.lhs.arg.this.apply(Set.Cup.eq.UnionCupS, cond={n})

    Eq << Set.CardUnion.eq.Sub_.AddCards.CardInter.principle.inclusion_exclusion.apply(*Eq[-1].rhs.args)

    Eq << Eq[0].subs(i, n).limits_subs(j, i)

    Eq << Set.EqCupS.of.All_Eq.apply(Eq[-1])

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq.induct.rhs.this.apply(Algebra.Sum.eq.Add.split, cond={n})

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Imply(Eq[1], Eq.induct, plausible=True)

    Eq << Logic.Cond.of.All_Imp.apply(Eq[-1], n=n, start=1)


if __name__ == '__main__':
    run()

# created on 2020-12-23
