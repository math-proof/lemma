from util import *


@apply
def apply(x_less_than_a, y_less_than_b):
    abs_x, a = x_less_than_a.of(Less)
    abs_y, b = y_less_than_b.of(Less)

    x = abs_x.of(Abs)
    y = abs_y.of(Abs)

    return Less(abs(x * y), a * b)


@prove
def prove(Eq):
    from Lemma import Algebra, Int
    x, y, a, b = Symbol(real=True)


    Eq << apply(abs(x) < a, abs(y) < b)

    Eq << Algebra.LtMul.of.Lt.Lt.apply(Eq[0], Eq[1])

    Eq << Eq[-1].this.lhs.apply(Int.MulAbsS.eq.AbsMul)


if __name__ == '__main__':
    run()
# created on 2020-01-07
