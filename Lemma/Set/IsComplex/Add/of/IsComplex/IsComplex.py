from util import *


@apply
def apply(a_is_complex, b_is_complex):
    a, C = a_is_complex.of(Element)
    assert C in S.Complexes
    b, C = b_is_complex.of(Element)
    assert C in S.Complexes
    return Element(a + b, S.Complexes)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, y = Symbol(super_complex=True)
    Eq << apply(Element(x, S.Complexes), Element(y, S.Complexes))

    Eq << Set.Any.Eq.of.In.apply(Eq[0], var='a')

    Eq << Set.Any.Eq.of.In.apply(Eq[1], var='b')

    Eq << Algebra.Any.And.of.Any.Any.apply(Eq[-1], Eq[-2], simplify=None)

    Eq << Eq[-1].this.expr.apply(Algebra.EqAdd.of.Eq.Eq)

    a, b = Eq[-1].variables
    c = Symbol(complex=True)
    Eq << Algebra.Any.of.Any.subst.apply(Eq[-1], a + b, c)




if __name__ == '__main__':
    run()
# created on 2023-05-03
