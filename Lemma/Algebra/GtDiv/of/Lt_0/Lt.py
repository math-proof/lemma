from util import *


@apply
def apply(lt_zero, lt):
    x = lt_zero.of(Expr < 0)
    assert x.is_finite
    lhs, rhs = lt.of(Less)
    lhs /= x
    rhs /= x
    lhs = lhs.ratsimp()
    rhs = rhs.ratsimp()
    return Greater(lhs, rhs)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, a, b = Symbol(real=True)
    Eq << apply(x < 0, a < b)

    Eq << Algebra.Div.lt.Zero.of.Lt_0.apply(Eq[0])

    Eq << Algebra.GtMul.of.Lt_0.Lt.apply(Eq[-1], Eq[1])





if __name__ == '__main__':
    run()
# created on 2019-07-15
# updated on 2023-04-11
