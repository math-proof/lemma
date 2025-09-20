from util import *


@apply
def apply(given):
    A, B = given.of(Element)

    return Equal({A} & B, {A})


@prove
def prove(Eq):
    from Lemma import Set

    e = Symbol(integer=True)
    s = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, s))

    Eq << Set.SubsetSingleton.of.In.apply(Eq[0], simplify=False)

    Eq << Set.EqInter.of.Subset.apply(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2020-10-28
