from util import *


@apply
def apply(given):
    x, y = given.of(GreaterEqual)
    return Equal(abs(x - y), x - y)


@prove
def prove(Eq):
    from Lemma import Algebra, Int

    x, y = Symbol(real=True)
    Eq << apply(x >= y)

    Eq << Algebra.Ge_0.of.Ge.apply(Eq[0])
    Eq << Int.EqAbs.of.Ge_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-05-25
