from util import *



@apply
def apply(given, simplify=True):
    e, domain = given.of(Element)
    A, B = domain.of(Union)

    first = Element(e, A)
    second = Element(e, B - A)

    if simplify:
        first = first.simplify()
        second = second.simplify()

    return Or(first, second)


@prove
def prove(Eq):
    from Lemma import Set
    e = Symbol(integer=True, given=True)
    A, B = Symbol(etype=dtype.integer, given=True)
    Eq << apply(Element(e, A | B))

    Eq << ~Eq[-1]

    Eq << Eq[-1].apply(Set.NotIn_Union.of.NotIn.NotIn)

    Eq <<= Eq[-1] & Eq[0]


if __name__ == '__main__':
    run()

# created on 2021-03-13
