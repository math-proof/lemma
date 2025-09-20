from util import *


@apply
def apply(greater_than, less_than):
    x, a = greater_than.of(GreaterEqual)
    y, b = less_than.of(LessEqual)

    return LessEqual((x - a) * (y - b), 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, a, b = Symbol(real=True)
    Eq << apply(x >= a, y <= b)

    Eq << Eq[1].reversed

    Eq << Algebra.Ge_0.of.Ge.Ge.apply(Eq[0], Eq[-1])

    Eq << -Eq[-1]

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[2].this.lhs.expand()


if __name__ == '__main__':
    run()
# created on 2019-06-03
