from util import *


@apply
def apply(greater_than, less_than):
    x, a = greater_than.of(GreaterEqual)
    y, b = less_than.of(GreaterEqual)

    return GreaterEqual((x - a) * (y - b), 0)


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y, a, b = Symbol(real=True)

    Eq << apply(x >= a, y >= b)

    Eq << Eq[0] - a

    Eq << Eq[1] - b

    Eq << Algebra.Ge_0.of.Ge_0.Ge_0.apply(Eq[-1], Eq[-2])


if __name__ == '__main__':
    run()
# created on 2019-05-19
