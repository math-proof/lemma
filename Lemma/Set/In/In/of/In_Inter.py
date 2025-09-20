from util import *


@apply
def apply(given, index=-1):
    e, domain = given.of(Element)
    s = domain.of(Intersection)
    if index is not None:
        first = s[:index]
        second = s[index:]
        return Element(e, Intersection(*first)), Element(e, Intersection(*second))
    else:
        return tuple(Element(e, s) for s in s)



@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(integer=True)
    A, B = Symbol(etype=dtype.integer)
    Eq << apply(Element(x, A & B))

    Eq << Set.In.of.In_Inter.apply(Eq[0], 0)
    Eq << Set.In.of.In_Inter.apply(Eq[0], 1)




if __name__ == '__main__':
    run()
# created on 2018-09-22
