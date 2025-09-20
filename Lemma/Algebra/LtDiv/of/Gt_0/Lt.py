from util import *


@apply
def apply(gt_zero, lt, *, simplify=True):
    x = gt_zero.of(Expr > 0)
    assert x.is_finite
    lhs, rhs = lt.of(Less)
    if lhs.is_infinite:
        ...
    else:
        lhs /= x

    if rhs.is_infinite:
        ...
    else:
        rhs /= x

    if simplify:
        lhs = lhs.ratsimp()
        rhs = rhs.ratsimp()
    return Less(lhs, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x > 0, a < b)

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[0])

    Eq << Algebra.LtMul.of.Gt_0.Lt.apply(Eq[-1], Eq[1])





if __name__ == '__main__':
    run()
# created on 2019-06-27
# updated on 2023-04-15
