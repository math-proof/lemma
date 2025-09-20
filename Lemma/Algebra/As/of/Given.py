from util import *


@apply
def apply(given, *, cond=None):
    lhs, rhs = given.of(Given)
    return Given(cond | lhs, cond | rhs)


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    p, q, r = Symbol(bool=True)
    Eq << apply(Given(p, q), cond=r)

    Eq << Logic.Or_Not.of.Imp.apply(Eq[0])

    Eq << Logic.ImpNot.given.Or.apply(Eq[1])

    Eq << Logic.Or_And.given.AndOrS.apply(Eq[-1])

    Eq << Algebra.Or.given.Or.apply(Eq[-1], slice(0, 3, 2))


if __name__ == '__main__':
    run()
# created on 2022-01-27
