from util import *


@apply
def apply(contains1, contains2):
    x, sx = contains1.of(Element)
    y, sy = contains2.of(Element)

    a, b = sx.of(Interval)
    _b, c = sy.of(Interval)
    if not sx.right_open and not sy.left_open:
        assert b < _b
    else:
        assert b <= _b

    return Less(x, y)


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    a, b, c, x, y = Symbol(integer=True, given=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True)), Element(y, Interval(b, c, left_open=True)))

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[0])

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[1])

    Eq << Algebra.Lt.of.Le.Gt.apply(Eq[-3], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2021-02-26
