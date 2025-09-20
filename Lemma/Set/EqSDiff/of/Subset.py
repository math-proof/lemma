from util import *


@apply
def apply(given):
    A, B = given.of(Subset)
    assert A.is_finiteset or B.is_finiteset
    return Equal(Card(B - A), Card(B) - Card(A))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    A = Symbol(etype=dtype.integer, finiteset=True)
    B = Symbol(etype=dtype.integer)
    Eq << apply(Subset(A, B, evaluate=False))

    Eq << Set.Card.eq.Add.split.apply(Card(B), A).reversed

    Eq << Set.EqInter.of.Subset.apply(Eq[0])

    Eq << Eq[-1].apply(Set.EqCard.of.Eq)

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Algebra.Eq.of.Eq.transport.apply(Eq[-1], lhs=0)





if __name__ == '__main__':
    run()

# created on 2021-06-26
# updated on 2023-06-01
