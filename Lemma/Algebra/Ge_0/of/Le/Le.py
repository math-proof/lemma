from util import *


@apply
def apply(less_than_0, less_than_1):
    x, a = less_than_0.of(LessEqual)
    y, b = less_than_1.of(LessEqual)

    return GreaterEqual((x - a) * (y - b), 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, a, b = Symbol(real=True)
    Eq << apply(x <= a, y <= b)

    Eq << Eq[0] - a

    Eq << Eq[1] - b

    Eq << Algebra.Ge_0.of.Le_0.Le_0.apply(Eq[-2], Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-10-26
