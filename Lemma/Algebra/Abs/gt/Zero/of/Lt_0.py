from util import *


@apply
def apply(given):
    x = given.of(Expr < 0)
    return Greater(abs(x), 0)


@prove
def prove(Eq):
    from Lemma import Algebra

    x = Symbol(real=True, given=True)
    Eq << apply(Less(x, 0))

    Eq << -Algebra.EqAbs.of.Lt_0.apply(Eq[0])

    Eq << Eq[0].subs(Eq[-1].reversed)

    Eq << -Eq[-1]


if __name__ == '__main__':
    run()
# created on 2020-01-17
