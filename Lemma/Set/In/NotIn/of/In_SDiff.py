from util import *


@apply
def apply(given):
    e, (A, B) = given.of(Element[Complement])
    return Element(e, A), NotElement(e, B)


@prove
def prove(Eq):
    from Lemma import Set

    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A - B))



    Eq << Eq[0].apply(Set.In.of.In_SDiff)

    Eq << Eq[0].apply(Set.NotIn.of.In_SDiff)


if __name__ == '__main__':
    run()

# created on 2018-01-13
