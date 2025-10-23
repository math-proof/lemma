from util import *


@apply
def apply(given):
    (xi, xj), *limits = given.of(All[Equal[Intersection, EmptySet]])
    * limits, (_, j_domain) = limits
    n_Interval, i = j_domain.of(Complement)
    n = n_Interval.stop
    i, *_ = i.args

    if not xi.has(i):
        xi = xj
        assert xj.has(i)

    eq = Equal(Card(Cup[i:n](xi)), Sum[i:n](Card(xi)))
    if limits:
        return All(eq, *limits)
    else:
        return eq


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Bool, Finset

    i, j = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo), given=False)
    x = Symbol(shape=(oo,), etype=dtype.integer, finiteset=True)
    i_domain = Range(n)
    Eq << apply(All(Equal(x[i] & x[j], x[i].etype.emptySet), (j, i_domain - {i})))

    Eq.initial = Eq[-1].subs(n, 2)

    Eq << Eq.initial.this.lhs.doit()

    Eq << Eq[-1].this.rhs.doit()

    Eq << Eq[0].subs(i, 1)

    Eq << Algebra.Cond.of.All.subst.apply(Eq[-1], j, 0)

    Eq << Set.CardUnion.eq.Sub_.AddCards.CardInter.principle.inclusion_exclusion.apply(*Eq[-1].lhs.args).subs(Eq[-1])

    Eq.induct = Eq[1].subs(n, n + 1)

    Eq << Eq.induct.lhs.arg.this.apply(Set.Cup.eq.UnionCupS, cond={n})

    Eq << Set.CardUnion.eq.Sub_.AddCards.CardInter.principle.inclusion_exclusion.apply(*Eq[-1].rhs.args)

    Eq << Eq[0].subs(i, n).limits_subs(j, i)

    Eq << Set.EqCupS.of.All_Eq.apply(Eq[-1])

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq.induct.rhs.this.apply(Finset.Sum.eq.AddSumS, cond={n})

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Imply(Eq[1], Eq.induct, plausible=True)

    Eq << Bool.Cond.of.Cond.All_Imp.apply(Eq.initial, Eq[-1], n=n, start=2)


if __name__ == '__main__':
    run()

# created on 2020-08-05
