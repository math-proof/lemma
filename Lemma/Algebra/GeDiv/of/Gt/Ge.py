from util import *


@apply
def apply(gt, ge):
    if ge.is_Less:
        gt, ge = ge, gt
    x, y = gt.of(Greater)
    z = x - y
    lhs, rhs = ge.of(GreaterEqual)
    return GreaterEqual(lhs / z, rhs / z)


@prove
def prove(Eq):
    from Lemma import Algebra
    x, y, a, b = Symbol(real=True)
    Eq << apply(x > y, a * (y - x) >= b)

    Eq << Algebra.Gt_0.of.Gt.apply(Eq[0])

    Eq << Algebra.GeDiv.of.Gt_0.Ge.apply(Eq[-1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2019-07-13
