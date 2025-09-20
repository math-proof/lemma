from util import *


@apply
def apply(x_less_than_a, y_less_than_a):
    x, a = x_less_than_a.of(Less)
    y, b = y_less_than_a.of(Less)
    return Less(Max(x, y), Max(a, b))


@prove
def prove(Eq):
    from Lemma import Algebra

    a, x, y, b = Symbol(real=True, given=True)
    Eq << apply(x < a, y < b)

    Eq << Algebra.GtMin.of.Gt.Gt.apply(-Eq[0], -Eq[1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Min.eq.Mul.Max)

    Eq << Eq[-1].this.rhs.apply(Algebra.Min.eq.Mul.Max)

    Eq << -Eq[-1]




if __name__ == '__main__':
    run()
# created on 2020-01-08
# updated on 2023-04-23
