from util import *


@apply
def apply(given, S):
    lhs, rhs = given.of(Element)
    if rhs in S:
        rhs = S
    else:
        rhs |= S
    return Element(lhs, rhs)


@prove
def prove(Eq):
    from Lemma import Set, Algebra, Bool

    e = Symbol(integer=True)
    U, S = Symbol(etype=dtype.integer)
    Eq << apply(Element(e, U), S)

    Eq << Set.In_Union.given.OrInS.apply(Eq[1])

    Eq << Bool.Or.given.Cond.apply(Eq[-1], index=1)


if __name__ == '__main__':
    run()


# created on 2018-01-11

