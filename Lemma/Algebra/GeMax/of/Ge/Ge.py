from util import *


@apply
def apply(ge_a, ge_b):
    x, a = ge_a.of(GreaterEqual)
    y, b = ge_b.of(GreaterEqual)
    return Max(x, y) >= Max(a, b)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, a, b = Symbol(real=True, given=True)
    Eq << apply(x >= a, y >= b)

    Eq << Algebra.LeMin.of.Le.Le.apply(-Eq[0], -Eq[1])

    Eq << Eq[-1].this.lhs.apply(Algebra.Min.eq.Mul.Max)

    Eq << Eq[-1].this.rhs.apply(Algebra.Min.eq.Mul.Max)

    Eq << -Eq[-1]




if __name__ == '__main__':
    run()
# created on 2019-05-16
# updated on 2023-04-23

