from util import *


@apply
def apply(given, *, cond=None):
    lhs, rhs = given.of(Given)
    return Given(cond | lhs, cond | rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool

    p, q, r = Symbol(bool=True)
    Eq << apply(Given(p, q), cond=r)

    Eq << Bool.Or_Not.of.Imp.apply(Eq[0])

    Eq << Bool.ImpNot.given.Or.apply(Eq[1])

    Eq << Bool.Or_And.given.AndOrS.apply(Eq[-1])

    Eq << Algebra.Or.given.Or.apply(Eq[-1], slice(0, 3, 2))


if __name__ == '__main__':
    run()
# created on 2022-01-27
