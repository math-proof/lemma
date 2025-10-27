from util import *


@apply
def apply(a_less_than_b, x_less_than_y):
    a, b = a_less_than_b.of(Less)
    x, y = x_less_than_y.of(Less)

    assert a >= 0
    assert x >= 0
    return Less(a * x, b * y)


@prove
def prove(Eq):
    from Lemma import Algebra, Int, Int, Nat
    a, x = Symbol(real=True, nonnegative=True)
    b, y = Symbol(real=True)

    Eq << apply(a < b, x < y)

    Eq << Eq[2] - x * b

    Eq << Eq[-1].this.lhs.collect(x)

    Eq << Eq[-1].this.rhs.collect(b)

    Eq << Eq[0].reversed

    Eq << Algebra.Gt.of.Gt.relax.apply(Eq[-1], 0)

    Eq << Eq[1] - x

    Eq.is_positive = Nat.Gt_0.of.Gt_0.Gt_0.apply(Eq[-1], Eq[-2])

    Eq << Eq[0] - a

    Eq << -Eq[-1]

    Eq << GreaterEqual(x, 0, plausible=True)

    Eq << Int.Le_0.of.Lt_0.Ge_0.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Lt.of.Gt.Le.apply(Eq.is_positive, Eq[-1])



if __name__ == '__main__':
    run()
# created on 2018-07-06
