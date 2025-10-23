from util import *


@apply
def apply(a_less_than_b, x_less_than_y):
    a, b = a_less_than_b.of(LessEqual)
    x, y = x_less_than_y.of(LessEqual)

    assert a.is_nonnegative
    assert x.is_nonnegative
    return LessEqual(a * x, b * y)


@prove
def prove(Eq):
    from Lemma import Algebra, Int, Int

    x, a = Symbol(real=True, nonnegative=True)
    b, y = Symbol(real=True)
    Eq << apply(a <= b, x <= y)

    Eq << Eq[2] - x * b

    Eq << Eq[-1].this.lhs.collect(x)

    Eq << Eq[-1].this.rhs.collect(b)

    Eq << Eq[0].reversed

    Eq << Algebra.Ge.of.Ge.relax.apply(Eq[-1], 0)

    Eq << Eq[1] - x

    Eq.is_nonnegative = Algebra.Ge_0.of.Ge_0.Ge_0.apply(Eq[-1], Eq[-2])

    Eq << Eq[0] - a

    Eq << -Eq[-1]

    Eq << GreaterEqual(x, 0, plausible=True)

    Eq << Int.Mul.le.Zero.of.Le_0.Ge_0.apply(Eq[-2], Eq[-1])

    Eq << Algebra.Le.of.Ge.Le.apply(Eq.is_nonnegative, Eq[-1])


if __name__ == '__main__':
    run()
# created on 2018-07-02
