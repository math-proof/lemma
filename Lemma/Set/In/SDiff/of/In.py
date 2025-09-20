from util import *


@apply
def apply(given, U):
    e, domain = given.of(Element)
    S, s = domain.of(Complement)
    assert S in U
    return Element(e, U - s)


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(integer=True)
    U, A, s = Symbol(etype=dtype.integer)
    S = Symbol(A & U)
    Eq << apply(Element(x, S - s), U)

    Eq << Subset(Eq[0].rhs, Eq[2].rhs, plausible=True)

    Eq << Set.In.of.In.Subset.apply(Eq[0], Eq[-1])


if __name__ == '__main__':
    run()

# created on 2021-03-03
