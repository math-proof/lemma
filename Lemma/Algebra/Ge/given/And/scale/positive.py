from util import *


@apply
def apply(given, scale, div=False):
    lhs, rhs = given.of(GreaterEqual)
    if div:
        ge = lhs / scale >= rhs / scale
    else:
        ge = lhs * scale >= rhs * scale
    return ge, scale > 0


@prove
def prove(Eq):
    from Lemma import Algebra, Rat

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(GreaterEqual(x, y), z)

    Eq << Rat.GeDivS.of.Ge.Gt_0.apply(Eq[2], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-05-22
