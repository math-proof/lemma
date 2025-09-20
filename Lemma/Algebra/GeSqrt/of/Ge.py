from util import *


def take_sqrt(x):
    if x.is_Pow:
        b, e = x.args
        if e.is_integer and e.is_even:
            return abs(b ** (e / 2))

    return sqrt(x)

@apply
def apply(given):
    lhs, rhs = given.of(GreaterEqual)
    assert rhs >= 0

    x = take_sqrt(lhs)
    y = take_sqrt(rhs)

    return GreaterEqual(x, y)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    Eq << apply(GreaterEqual(x * x, y * y))

    Eq << Algebra.LeSqrt.of.Le.apply(Eq[0].reversed)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()

# created on 2019-05-31
