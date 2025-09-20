from util import *


@apply
def apply(gt):
    lhs, rhs = gt.of(Greater)
    return log(lhs) > log(rhs)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Greater(x, y))

    Eq << Algebra.GtExp.of.Gt.apply(Eq[1])


if __name__ == '__main__':
    run()
# created on 2023-04-16
