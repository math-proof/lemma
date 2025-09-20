from util import *


@apply
def apply(gt, contains_y):
    y, _a = gt.of(Greater)
    S[y], domain = contains_y.of(Element)
    a, b = domain.of(Interval)
    a = Max(a, _a)
    return Element(y, Interval(a, b, left_open=True, right_open=domain.right_open))


@prove
def prove(Eq):
    from Lemma import Set

    a, b, x, y = Symbol(real=True)
    Eq << apply(x > a, Element(x, Interval(a, b)))

    Eq << Set.In_Ico.given.Ge.Lt.apply(Eq[2])

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2018-06-21
