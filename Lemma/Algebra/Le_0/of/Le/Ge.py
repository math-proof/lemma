from util import *



@apply
def apply(less_than_0, greater_than):
    x, a = less_than_0.of(LessEqual)
    y, b = greater_than.of(GreaterEqual)

    return LessEqual((x - a) * (y - b), 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, a, b = Symbol(real=True)
    Eq << apply(x <= a, y >= b)

    Eq << Eq[1].reversed

    Eq << Algebra.Ge_0.of.Le.Le.apply(Eq[0], Eq[-1])

    Eq << -Eq[-1]

    Eq << Eq[-1].this.lhs.expand()

    Eq << Eq[2].this.lhs.expand()


if __name__ == '__main__':
    run()

# created on 2019-10-27
