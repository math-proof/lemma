from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    return Unequal(Card(A), 0)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Logic

    A = Symbol(etype=dtype.integer)
    Eq << apply(Unequal(A, A.etype.emptySet))

    Eq << Set.Any_In.of.Ne_Empty.apply(Eq[0], simplify=False)

    Eq << Eq[-1].this.expr.apply(Set.EqUnion.of.In)

    Eq << Eq[-1].this.expr.apply(Set.EqCard.of.Eq)

    Eq << Eq[-1].this.find(Card).apply(Set.Card.eq.Add)

    Eq << Unequal(Eq[-1].find(Add), 0, plausible=True)

    Eq << Logic.Any_And.of.Any.All.apply(Eq[-2], Eq[-1])


    Eq << Eq[-1].this.expr.apply(Algebra.Ne.of.Eq.Ne)




if __name__ == '__main__':
    run()

# created on 2020-07-11
# updated on 2023-06-01
