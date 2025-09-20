from util import *


@apply
def apply(given, index=0):
    e, domain = given.of(Element)
    s = domain.of(Intersection)
    if isinstance(index, slice):
        s = Intersection(*s[index])
    else:
        s = s[index]
    return Element(e, s)


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Element(x, A & B), index=0)

    Eq << Subset(A & B, A, plausible=True)

    Eq << Set.In.of.In.Subset.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2018-07-23
