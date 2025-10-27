from util import *


@apply
def apply(is_negative, lt):
    x = is_negative.of(Expr < 0)
    assert x.is_finite
    lhs, rhs = lt.of(Less)
    return Greater(lhs * x, rhs * x)


@prove
def prove(Eq):
    from Lemma import Algebra, Int

    x, a, b = Symbol(real=True)
    Eq << apply(x < 0, a < b)

    Eq << Eq[1] - b

    Eq << Int.Gt_0.of.Lt_0.Lt_0.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] + b * x


if __name__ == '__main__':
    run()
# created on 2019-07-14
