from util import *


@apply
def apply(given, reverse=False):
    S_abs, n = given.of(Equal)

    assert n.is_extended_positive
    S = S_abs.of(Card)
    x = S.element_symbol()
    if reverse:
        eq = Equal(S, x.set)
    else:
        eq = Equal(x.set, S)
    return Any[x](eq)


@prove
def prove(Eq):
    from Lemma import Set

    S = Symbol(etype=dtype.integer)
    Eq << apply(Equal(Card(S), 1))

    Eq << Greater(Card(S), 0, plausible=True)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Set.Ne_Empty.of.Gt_0.apply(Eq[-1])

    Eq << Set.Any_In.of.Ne_Empty.apply(Eq[-1], simplify=False)

    Eq << Eq[-1].this.expr.apply(Set.SubsetSingleton.of.In, simplify=False)

    Eq << Eq[-1].this.expr.apply(Set.Eq.of.Eq_Card.Subset, Eq[0])


if __name__ == '__main__':
    run()

# created on 2020-07-21
