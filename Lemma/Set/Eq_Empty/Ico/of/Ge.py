from util import *


@apply
def apply(given):
    a, b = given.of(GreaterEqual)
    assert a.is_integer and b.is_integer
    return Equal(Range(a, b), a.emptySet)


@prove
def prove(Eq):
    from Lemma import Set

    x, y = Symbol(integer=True, given=True)
    Eq << apply(x >= y)

    Eq << ~Eq[1]

    Eq << Set.Lt.of.Ico_Ne_Empty.apply(Eq[-1])

    Eq << ~Eq[-1]


if __name__ == '__main__':
    run()
# created on 2018-10-19
