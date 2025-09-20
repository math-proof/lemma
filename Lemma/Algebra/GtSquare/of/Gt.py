from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Greater)
    assert rhs >= 0 or rhs.of(Expr ** (S.One / 2))

    return Greater(lhs * lhs, rhs * rhs)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True)
    y = Symbol(real=True, nonnegative=True)
    Eq << apply(Greater(x, y))

    Eq << Algebra.GtMul.of.Gt.Gt.apply(Eq[0], Eq[0])


if __name__ == '__main__':
    run()

# created on 2018-07-07
