from util import *


@apply
def apply(given, index=-1):
    args = given.of(Equal[Union, EmptySet])
    lhs = Union(*args[:index])
    rhs = Union(*args[index:])
    emptySet = lhs.etype.emptySet
    return Equal(lhs, emptySet), Equal(rhs, emptySet)


@prove
def prove(Eq):
    from Lemma import Set

    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Equal(A | B, A.etype.emptySet))

    Eq << Set.Eq_Empty.of.Eq_Empty.apply(Eq[0], index=0)

    Eq << Set.Eq_Empty.of.Eq_Empty.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()

# created on 2021-05-13
