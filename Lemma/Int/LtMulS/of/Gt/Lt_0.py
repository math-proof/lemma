from util import *


@apply
def apply(lt_zero, gt):
    x = lt_zero.of(Expr < 0)
    assert x.is_finite
    lhs, rhs = gt.of(Greater)
    return Less(lhs * x, rhs * x)


@prove
def prove(Eq):
    from Lemma import Int

    x, a, b = Symbol(real=True)
    Eq << apply(x < 0, a > b)

    Eq << Eq[1] - b

    Eq << Int.Gt0Mul.of.Gt_0.Lt_0.apply(Eq[0], Eq[-1])

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[-1] + b * x


if __name__ == '__main__':
    run()
# created on 2019-12-15
