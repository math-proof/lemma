from util import *


@apply
def apply(is_complex):
    a, C = is_complex.of(Element)
    assert C in S.Complexes
    return Element(~a, S.Complexes)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, y = Symbol(super_complex=True)
    Eq << apply(Element(x, S.Complexes))

    Eq << Set.Any.Eq.of.In.apply(Eq[0], var='a')

    Eq << Eq[-1].this.expr.apply(Algebra.EqConj.of.Eq)

    a = Eq[-1].variable

    c = Symbol(complex=True)
    Eq << Algebra.Any.of.Any.subst.apply(Eq[-1], ~a, c)



if __name__ == '__main__':
    run()
# created on 2023-05-03
