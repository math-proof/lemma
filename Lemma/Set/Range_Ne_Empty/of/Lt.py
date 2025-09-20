from util import *


@apply
def apply(given):
    a, b = given.of(Less)
    assert a.is_integer and b.is_integer
    return Unequal(Range(a, b), a.emptySet)


@prove
def prove(Eq):
    from Lemma import Set

    a, b = Symbol(integer=True, given=True)
    Eq << apply(b < a)

    Eq << Eq[0].reversed
    Eq << Set.Range_Ne_Empty.of.Gt.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-05-30
