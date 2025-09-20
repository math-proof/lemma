from util import *


@apply
def apply(eq, sgm):
    (ai, (i, S[0], n)), X = eq.of(Equal[Cup[FiniteSet]])
    S[X] = n.of(Card)
    fx, (x, S[X]) = sgm.of(Sum)

    return Equal(sgm, Sum[i:n](fx._subs(x, ai)))


@prove
def prove(Eq):
    from Lemma import Set

    X = Symbol(etype=dtype.real, empty=False)
    x = Symbol(real=True)
    a = Symbol(real=True, shape=(oo,))
    f = Function(real=True)
    Eq << apply(Equal(X, a[:Card(X)].cup_finiteset()), Sum[x:X](f(x)))

    n = Symbol(Card(X))
    Eq << n.this.definition.reversed

    Eq << Eq[0].subs(Eq[-1])

    Eq << Set.EqSum.of.Eq_Cup.Eq_Card.apply(Eq[-1], Eq[-2], Eq[1].lhs)

    Eq << Eq[1].subs(Eq[2])


if __name__ == '__main__':
    run()
# created on 2021-03-21

from . import Eq_Card
from . import Eq_Cup
