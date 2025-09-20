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
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(GreaterEqual(x, y), z)

    Eq << Algebra.GeDiv.of.Gt_0.Ge.apply(Eq[2], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-05-22
