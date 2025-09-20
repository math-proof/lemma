from util import *


# given e not in S


# => S - {e} = S
@apply
def apply(given):
    e, S = given.of(NotElement)
    return Equal(S - {e}, S)


@prove
def prove(Eq):
    from Lemma import Set

    S = Symbol(etype=dtype.integer)
    e = Symbol(integer=True)
    Eq << apply(NotElement(e, S))

    Eq << Set.Eq_Empty.Inter.of.NotIn.apply(Eq[0])

    Eq << Set.EqSDiff.of.Inter_Eq_Empty.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-02-01
