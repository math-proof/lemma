from util import *


@apply
def apply(is_complex):
    x, C = is_complex.of(Element)
    assert C in S.Complexes
    return Element(x * ~x, Interval(0, oo))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x = Symbol(super_complex=True)
    Eq << apply(Element(x, S.Complexes))

    Eq << Set.Eq.of.In.definition.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(Algebra.Expr.eq.AddRe_MulIIm)

    Eq << Eq[1].subs(Eq[-1].reversed)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS, deep=True)


if __name__ == '__main__':
    run()
# created on 2023-05-03
