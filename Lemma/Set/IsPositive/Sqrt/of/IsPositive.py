from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval.open(0, oo)
    return Element(sqrt(x), R)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x = Symbol(super_complex=True)
    Eq << apply(Element(x, Interval.open(0, oo)))

    Eq << Set.IsReal.of.IsPositive.apply(Eq[0])

    Eq << Set.Eq.of.In.definition.apply(Eq[-1])

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << Set.Gt_0.of.IsPositive.apply(Eq[-1])

    Eq << Algebra.Gt_0.Sqrt.of.Gt_0.apply(Eq[-1], simplify=None)

    Eq << Set.IsPositive.of.Gt_0.apply(Eq[-1], simplify=None)

    Eq << Eq[-1].subs(Eq[3])




if __name__ == '__main__':
    run()
# created on 2023-05-03
