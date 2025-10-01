from util import *


@apply
def apply(a_is_real, b_is_real):
    a, aR = a_is_real.of(Element)
    b, bR = b_is_real.of(Element)
    from Lemma.Set.IsReal.of.IsReal.IsReal import interval_is_real
    assert interval_is_real(aR)
    assert interval_is_real(bR)
    return Element(a - b, Reals)


@prove
def prove(Eq):
    from Lemma import Set

    x, y = Symbol(hyper_real=True)
    Eq << apply(Element(x, Reals), Element(y, Reals))

    Eq << Set.Neg.In.Icc.of.In_Icc.apply(Eq[1])

    Eq << Set.IsReal.Add.of.IsReal.IsReal.apply(Eq[-1], Eq[0])


if __name__ == '__main__':
    run()
# created on 2022-04-03
