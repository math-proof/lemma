from util import *


@apply
def apply(is_positive_x, strict_greater_than):
    x = is_positive_x.of(Expr > 0)
    assert x.is_finite
    lhs, rhs = strict_greater_than.of(Greater)
    return Greater(lhs * x, rhs * x)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x > 0, a > b)

    Eq << Eq[1] - b

    Eq << Algebra.Gt_0.of.Gt_0.Gt_0.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] + b * x


if __name__ == '__main__':
    run()
# created on 2019-06-11
