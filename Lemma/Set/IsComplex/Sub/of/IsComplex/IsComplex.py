from util import *


@apply
def apply(a_is_complex, b_is_complex):
    a, C = a_is_complex.of(Element)
    assert C in S.Complexes
    b, C = b_is_complex.of(Element)
    assert C in S.Complexes
    return Element(a - b, S.Complexes)


@prove
def prove(Eq):
    from Lemma import Set

    x, y = Symbol(super_complex=True)
    Eq << apply(Element(x, S.Complexes), Element(y, S.Complexes))

    Eq << Set.IsComplex.Neg.of.IsComplex.apply(Eq[1])

    Eq << Set.IsComplex.Add.of.IsComplex.IsComplex.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2023-05-03
