from util import *


@apply
def apply(given):
    lhs, rhs = given.of(Greater)
    assert rhs >= 0
    return Greater(sqrt(lhs), sqrt(rhs))


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True, given=True)
    Eq << apply(Greater(x * x, y * y))

    Eq << Algebra.LtSqrt.of.Lt.apply(Eq[0].reversed)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2019-07-01
