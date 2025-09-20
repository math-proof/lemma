from util import *


@apply
def apply(given):
    A = given.of(Unequal[EmptySet])
    a, b = A.of(Range)
    return LessEqual(a - b, 0)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Unequal(Range(a, b), a.emptySet))

    Eq << Set.Le.of.Range_Ne_Empty.apply(Eq[0])

    Eq << Algebra.Le_0.of.Le.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-06-23
