from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Range)
    return Less(a - b, 0)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Unequal(Range(a, b), a.emptySet))

    Eq << Set.Lt.of.Ico_Ne_Empty.apply(Eq[0])
    Eq << Algebra.Lt_0.of.Lt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-06-24
