from util import *


@apply
def apply(contains):
    x, domain = contains.of(Element)
    assert domain in Interval(-1, 0, left_open=True)
    return Equal(Ceil(x), 0)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x = Symbol(real=True)
    Eq << apply(Element(x, Interval(-1, 0, left_open=True)))

    Eq << Set.Neg.In.IccNegS.of.In_Icc.apply(Eq[0])

    Eq << Set.Floor.eq.Zero.of.In_Ico.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Floor.eq.Neg.Ceil)
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2018-10-22
