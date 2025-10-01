from util import *


@apply
def apply(given, S):
    lhs, rhs = given.of(Element)
    if S in rhs:
        rhs = S
    else:
        rhs &= S
    return Element(lhs, rhs)


@prove
def prove(Eq):
    from Lemma import Set

    e = Symbol(integer=True)
    U, S = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, U), S)

    Eq << Set.In.In.of.In_Inter.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2022-01-28
