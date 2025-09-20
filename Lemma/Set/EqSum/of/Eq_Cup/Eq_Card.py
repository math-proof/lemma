from util import *


@apply
def apply(eq, eq_abs, sgm):
    ((a, i), (S[i], S[0], n)), X = eq.of(Equal[Cup[FiniteSet[Indexed]]])

    S[X], S[n] = eq_abs.of(Equal[Card])
    fx, (x, S[X]) = sgm.of(Sum)

    return Equal(sgm, Sum[i:n](fx._subs(x, a[i])))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    n = Symbol(integer=True, positive=True)
    X = Symbol(etype=dtype.real)
    x = Symbol(real=True)
    a = Symbol(real=True, shape=(oo,))
    f = Function(real=True)
    Eq << apply(Equal(X, a[:n].cup_finiteset()), Equal(Card(X), n), Sum[x:X](f(x)))

    Eq << Eq[1].subs(Eq[0])

    fx, (x, X) = Eq[2].lhs.of(Sum)
    Eq << Set.EqSum.of.Eq_Card.apply(Eq[-1], Sum[x:Eq[-1].lhs.arg](fx))
    Eq << Eq[-1].subs(Eq[0].reversed)


if __name__ == '__main__':
    run()
# created on 2021-03-21
