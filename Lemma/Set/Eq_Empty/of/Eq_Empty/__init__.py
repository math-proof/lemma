from util import *


@apply
def apply(given, index=0):
    args = given.of(Equal[Union, EmptySet])
    A = args[index]
    emptySet = A.etype.emptySet
    return Equal(A, emptySet)


@prove
def prove(Eq):
    from Lemma import Set

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Equal(A | B, A.etype.emptySet))

    Eq.A_nonempty = ~Eq[-1]

    Eq.A_positive = Eq.A_nonempty.apply(Set.Gt_0.of.Ne_Empty)

    Eq << Eq[0].apply(Set.EqCard.of.Eq)

    Eq << Eq[-1].this.lhs.apply(Set.Card.eq.Add, slice(1, None))

    Eq << Set.EqSDiff.of.Eq.apply(Eq[0], A)

    Eq << Eq[-1].apply(Set.EqCard.of.Eq)

    Eq << Eq[-3].subs(Eq[-1])


    Eq << Eq.A_positive.subs(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2021-05-13
# updated on 2023-06-01

del Subset
from . import Subset
