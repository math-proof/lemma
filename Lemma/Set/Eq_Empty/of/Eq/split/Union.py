from util import *


@apply
def apply(given):
    x_union_abs, x_abs_sum = given.of(Equal)
    if not x_union_abs.is_Card:
        x_union_abs, x_abs_sum = x_abs_sum, x_union_abs

    A, B = x_union_abs.of(Card[Union])

    S[Card(A)] = x_abs_sum.of(Add[Card(B)])

    return Equal(A & B, A.etype.emptySet)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Equal(Card(A | B), Card(A) + Card(B)))

    Eq << Set.CardUnion.eq.Sub_.AddCards.CardInter.principle.inclusion_exclusion.apply(A, B)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-1].this.apply(Algebra.EqAddS.Is.Eq)

    Eq << -Eq[-1]

    Eq << Eq[-1].apply(Set.Eq_Empty.of.Eq_0)


if __name__ == '__main__':
    run()

# created on 2021-04-04
