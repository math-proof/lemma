from util import *


@apply
def apply(given):
    x = given.of(Expr < 0)
    return Equal(sign(x), -1)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(complex=True)
    Eq << apply(x < 0)

    Eq << -Eq[0]

    Eq << Algebra.EqSign.of.Gt_0.apply(Eq[-1])

    Eq << -Eq[-1]


if __name__ == '__main__':
    run()
# created on 2023-05-29
