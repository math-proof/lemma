from util import *


@apply
def apply(imply):
    e, S = imply.of(Element)
    a, b = S.of(Interval)
    assert S.left_open
    return Element(e, Interval(a, b, right_open=S.right_open))


@prove
def prove(Eq):
    from Lemma import Set, Algebra

    x, a, b = Symbol(real=True)
    Eq << apply(Element(x, Interval(a, b, left_open=True, right_open=True)))

    Eq << Set.In_Ico.given.Ge.Lt.apply(Eq[1])

    Eq << Set.Ge.Le.of.In_Icc.apply(Eq[0])

    Eq << Algebra.Ge.of.Gt.relax.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2021-02-27
