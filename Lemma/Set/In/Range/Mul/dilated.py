from util import *


@apply
def apply(given, d):
    d = sympify(d)
    assert d.is_positive
    assert d.is_integer

    e, (a, b) = given.of(Element[Range])

    e *= d

    return Element(e, Range(a * d, (b - 1) * d + 1, d))


@prove
def prove(Eq):
    from Lemma import Algebra, Set, Logic

    x, a, b = Symbol(integer=True)
    d = Symbol(integer=True, positive=True)
    Eq << apply(Element(x, Range(a, b)), d)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Set.In.Mul.Range.of.In.dilated, d)

    Eq << Eq[-1].this.rhs.apply(Set.In.given.In.Mul.Range.dilated, d)


if __name__ == '__main__':
    run()
# created on 2023-05-30
