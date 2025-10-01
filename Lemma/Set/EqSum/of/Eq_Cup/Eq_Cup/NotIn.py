from util import *


@apply
def apply(eq_cup, eq_cup_union, notcontains, sgm, *, assumptions=None):
    ((a, i), (S[i], S[0], n)), X = eq_cup.of(Equal[Cup[FiniteSet[Indexed]]])

    ((b, S[i]), (S[i], S[0], S[n + 1])), X_union = eq_cup_union.of(Equal[Cup[FiniteSet[Indexed]]])

    y, S[X] = X_union.of(Union[FiniteSet, Basic])

    fbi, (i, S[0], S[n + 1]) = sgm.of(Sum)

    S[X] = n.of(Card)

    S[y], S[X] = notcontains.of(NotElement)

    if assumptions is None:
        assumptions = {}
    if i not in assumptions:
        assumptions[i] = False

    return Equal(sgm, Sum[i:n](fbi._subs(b[i], a[i], assumptions=assumptions)) + fbi._subs(b[i], y, assumptions=assumptions))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    i = Symbol(integer=True)
    X = Symbol(etype=dtype.real)
    x, y = Symbol(real=True)
    a, b = Symbol(real=True, shape=(oo,))
    f = Function(real=True)
    n = Card(X)
    Eq << apply(Equal(X, a[:n].cup_finiteset()), Equal(X | {y}, b[:n + 1].cup_finiteset()), NotElement(y, X), Sum[i:n + 1](f(b[i])))

    Eq << Set.EqSum.of.Eq_Cup.apply(Eq[0], Sum[x:X](f(x)))

    Eq.plausible = Eq[3].subs(Eq[-1].reversed)

    Eq << Set.EqCard.of.NotIn.apply(Eq[2])

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Set.EqSum.of.Eq_Cup.apply(Eq[-1], Sum[x:X | {y}](f(x)))

    Eq << Eq[-1].subs(Eq[-3])

    Eq << Eq.plausible.subs(Eq[-1].reversed)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.AddSumS, cond={y})

    Eq << Set.EqSDiff.of.NotIn.apply(Eq[2])

    Eq << Eq[-2].subs(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-03-23
