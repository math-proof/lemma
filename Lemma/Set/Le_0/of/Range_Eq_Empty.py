from util import *


@apply
def apply(given):
    A = given.of(Equal[EmptySet])
    a, b = A.of(Range)
    return LessEqual(b - a, 0)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b = Symbol(integer=True, given=True)
    Eq << apply(Equal(Range(a, b), a.emptySet))

    Eq << Set.Le.of.Range_Eq_Empty.apply(Eq[0])

    Eq << Algebra.Le_0.of.Le.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-06-19
