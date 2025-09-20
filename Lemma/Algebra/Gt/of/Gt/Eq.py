from util import *


@apply
def apply(gt, eq):
    from Lemma.Algebra.Lt.of.Lt.Eq import swap
    return Greater(*swap(Greater, gt, eq))


@prove
def prove(Eq):
    from Lemma import Algebra

    a, x, b = Symbol(real=True)
    # Eq << apply(b > x, Equal(x, a))
    Eq << apply(b > x, Equal(a, x))

    Eq << Eq[0] + Eq[1].reversed

    Eq << Eq[-1].this.apply(Algebra.GtAddS.Is.Gt)


if __name__ == '__main__':
    run()
# created on 2018-06-29

