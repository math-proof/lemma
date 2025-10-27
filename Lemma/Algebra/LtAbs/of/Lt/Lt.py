from util import *


@apply
def apply(x_less_than_y, neg_x_less_than_y):
    x, y = x_less_than_y.of(Less)
    S[-x], S[y] = neg_x_less_than_y.of(Less)
    return Less(abs(x), y)


@prove
def prove(Eq):
    from Lemma import Algebra, Int, Nat
    x, y = Symbol(real=True)

    Eq << apply(x < y, -x < y)

    Eq << Eq[0] - y

    Eq << Eq[1] - y

    Eq << Int.Gt_0.of.Lt_0.Lt_0.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.lhs.expand() + x * x

    Eq << Eq[-1].reversed

    Eq.lt = Algebra.LtSqrt.of.Lt.apply(Eq[-1])

    Eq << Nat.Gt.of.Lt.Gt.apply(Eq[0], -Eq[1])

    Eq << (Eq[-1] + y) / 2

    Eq << Int.EqAbs.of.Gt_0.apply(Eq[-1])

    Eq << Eq.lt.subs(Eq[-1])


if __name__ == '__main__':
    run()

# created on 2019-12-30

