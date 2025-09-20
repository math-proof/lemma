from util import *


@apply
def apply(given):
    B, A = given.of(Equal[Card[Complement], 0])
    return Subset(B, A)


@prove
def prove(Eq):
    from Lemma import Set
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Equal(0, Card(B - A)))

    Eq << Set.Eq_Empty.of.Eq_0.apply(Eq[0])

    Eq << Set.Subset.SDiff.of.Eq_Empty.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-09-06
