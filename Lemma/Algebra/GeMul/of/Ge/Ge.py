from util import *



@apply
def apply(a_less_than_b, x_less_than_y):
    a, b = a_less_than_b.of(GreaterEqual)
    x, y = x_less_than_y.of(GreaterEqual)

    assert b.is_nonnegative
    assert y.is_nonnegative
    return GreaterEqual(a * x, b * y)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat
    a, x = Symbol(real=True)
    b, y = Symbol(real=True, nonnegative=True)

    Eq << apply(a >= b, x >= y)

    Eq << Nat.LeMulS.of.Le.Le.Ge_0.Ge_0.apply(Eq[0].reversed, Eq[1].reversed)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-01-10
