from util import *


@apply
def apply(given):
    x, R = given.of(Element)
    start, stop = R.of(Interval)
    if R.left_open:
        assert start >= 0
    else:
        assert start > 0
    assert stop == oo
    assert x.is_complex

    return Greater(x, 0)


@prove
def prove(Eq):
    from Lemma import Set

    x = Symbol(complex=True, given=True)
    Eq << apply(Element(x, Interval.open(0, oo)))



    Eq << Set.In.Icc.of.Gt.apply(Eq[1])




if __name__ == '__main__':
    run()
# created on 2020-05-16
