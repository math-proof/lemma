from util import *


@apply
def apply(ge):
    x, a = ge.of(GreaterEqual)
    assert a > 0

    return LessEqual(1 / x, 1 / a)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True)
    a = Symbol(real=True, positive=True)
    Eq << apply(x >= a)

    Eq << Algebra.Gt_0.of.Ge.apply(Eq[0])

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[-1])

    Eq << Algebra.GeMul.of.Gt_0.Ge.apply(Eq[-1], Eq[0])

    Eq << Eq[1] * a


if __name__ == '__main__':
    run()
# created on 2019-06-02
