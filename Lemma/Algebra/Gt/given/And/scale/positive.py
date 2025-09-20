from util import *


@apply
def apply(given, scale, div=False):
    lhs, rhs = given.of(Greater)
    if div:
        gt = lhs / scale > rhs / scale
    else:
        gt = lhs * scale > rhs * scale
    return gt, scale > 0


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Greater(x, y), z)

    Eq << Algebra.GtDiv.of.Gt_0.Gt.apply(Eq[2], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-07-16
