from util import *


@apply
def apply(el):
    x, domain = el.of(Element)
    a, b = domain.of(Interval)
    assert domain.right_open
    if domain.left_open:
        assert a.is_infinite
    else:
        if not a.is_integer:
            a = Floor(a)

    if not b.is_integer:
        b = Ceil(b)

    return Element(Floor(x), Range(a, b))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, x = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, right_open=True)))

    Eq << Set.Neg.In.Icc.of.In_Icc.apply(Eq[0])

    Eq << Set.In_Ico.Ceil.of.In_Icc.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Ceil.eq.Neg.Floor)

    Eq << Set.Neg.In.Icc.of.In_Icc.apply(Eq[-1])

    Eq << Eq[-1].this.find(-~Ceil).apply(Algebra.Ceil.eq.Neg.Floor)

    Eq << Eq[-1].this.find(-~Floor).apply(Algebra.Floor.eq.Neg.Ceil)




if __name__ == '__main__':
    run()
# created on 2021-03-05
# updated on 2023-04-17
