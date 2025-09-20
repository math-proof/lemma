from util import *


@apply
def apply(given, var=None):
    S, n = given.of(Equal[Card])

    assert n.is_extended_positive
    if var is None:
        var = S.element_symbol()
    return Any[var:S](Equal(Card(S - var.set), n - 1))


@prove
def prove(Eq):
    from Lemma import Algebra, Set

    S = Symbol(etype=dtype.integer)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Equal(Card(S), n))

    Eq << Algebra.Ge.of.Eq.apply(Eq[0])

    Eq << Set.Any_In.of.Ge.apply(Eq[-1], simplify=False)

    Eq << Set.Any_In.of.Any_In.limits_restricted.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.expr.apply(Set.EqUnion.of.In)

    Eq << Eq[-1].this.expr.apply(Set.EqCard.of.Eq)

    Eq << Eq[-1].this.find(Card).apply(Set.Card.eq.Add)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.expr - 1







if __name__ == '__main__':
    run()

# created on 2020-09-07
# updated on 2023-06-01
