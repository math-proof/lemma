from util import *


@apply
def apply(gt, index=-1):
    args, x = gt.of(Min > Expr)
    first = args[:index]
    second = args[index:]

    return Greater(Min(*first), x), Greater(Min(*second), x)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(Min(y, z) > x)

    Eq << Algebra.Gt.of.Gt_Min.apply(Eq[0], index=0)

    Eq << Algebra.Gt.of.Gt_Min.apply(Eq[0], index=1)


if __name__ == '__main__':
    run()
# created on 2019-08-05
