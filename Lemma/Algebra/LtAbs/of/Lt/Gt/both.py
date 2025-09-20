from util import *


@apply
def apply(x_less_than_y, x_greater_than_y_minus):
    x, y = x_less_than_y.of(Less)
    S[x], S[-y] = x_greater_than_y_minus.of(Greater)
    return Less(abs(x), abs(y))


@prove
def prove(Eq):
    from Lemma import Algebra
    y, x = Symbol(real=True)

    Eq << apply(x < y, x > -y)

    Eq << Algebra.Gt.of.Lt.Gt.apply(Eq[0], Eq[1])

    Eq << Eq[-1] + y

    Eq << Eq[-1] / 2

    Eq << Algebra.EqAbs.of.Gt_0.apply(Eq[-1])

    Eq << Algebra.LtAbs.of.Lt.Gt.apply(Eq[0], Eq[1])

    Eq << Eq[-1] + Eq[-2].reversed

    Eq << Eq[-1].this.apply(Algebra.LtAddS.Is.Lt)

if __name__ == '__main__':
    run()
# created on 2019-12-18
