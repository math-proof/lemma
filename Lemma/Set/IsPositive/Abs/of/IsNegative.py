from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    assert R in Interval.open(-oo, 0)
    return Element(abs(x), -R)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x = Symbol(complex=True)
    Eq << apply(Element(x, Interval.open(-oo, 0)))

    Eq << Set.Lt_0.of.IsNegative.apply(Eq[0])

    Eq << Algebra.EqAbs.of.Lt_0.apply(Eq[-1])

    Eq << Eq[1].subs(Eq[-1])

    Eq << Set.Neg.In.IccNegS.of.In_Icc.apply(Eq[0], simplify=None)




if __name__ == '__main__':
    run()
# created on 2020-04-15
# updated on 2023-04-18
