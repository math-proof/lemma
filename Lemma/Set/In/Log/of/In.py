from util import *


@apply
def apply(given):
    e, interval = given.of(Element)
    start, stop = interval.of(Interval)
    left_open = interval.left_open
    right_open = interval.right_open

    if left_open:
        if start > 0:
            start = log(start)
        elif start == 0:
            start = -oo
        else:
            return
    else:
        assert start > 0
        start = log(start)

    stop = log(stop)

    return Element(log(e), Interval(start, stop, left_open=left_open, right_open=right_open))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, b = Symbol(real=True)
    a = Symbol(real=True, positive=True)
    Eq << apply(Element(x, Interval(a, b)))

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[0])

    Eq << Algebra.GeLog.of.Ge.apply(Eq[-2])

    Eq << Algebra.Gt_0.of.Ge.apply(Eq[2])
    Eq << Algebra.LeLog.of.Gt_0.Le.apply(Eq[-1], Eq[3])

    Eq << Set.In_Ico.given.Ge.Lt.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2021-03-05
