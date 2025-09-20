from util import *


@apply
def apply(given):
    x, y = given.of(Greater)
    return Equal(abs(x - y), x - y)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y = Symbol(real=True)
    Eq << apply(x > y)

    Eq << Algebra.Gt_0.of.Gt.apply(Eq[0])
    Eq << Algebra.EqAbs.of.Gt_0.apply(Eq[-1])


if __name__ == '__main__':
    run()
# created on 2019-07-21
