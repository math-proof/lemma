from util import *


@apply
def apply(ge_zero, is_complex):
    x = ge_zero.of(Expr >= 0)
    S[x], C = is_complex.of(Element)
    assert C in S.Complexes
    return Element(x, Interval(0, oo))


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(super_complex=True)
    Eq << apply(x >= 0, Element(x, S.Complexes))

    Eq << Set.Eq.of.In.definition.apply(Eq[1])

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << Set.IsNotNegative.of.Ge_0.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].subs(Eq[3])


if __name__ == '__main__':
    run()
# created on 2023-05-03
