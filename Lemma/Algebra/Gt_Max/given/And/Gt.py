from util import *


@apply
def apply(gt, index=-1):
    x, args = gt.of(Expr > Max)
    first = args[:index]
    second = args[index:]

    return x > Max(*first), x > Max(*second)


@prove
def prove(Eq):
    from Lemma import Algebra

    x, y, z = Symbol(real=True, given=True)
    Eq << apply(x > Max(y, z))

    Eq << Algebra.GtMax.of.Gt.Gt.apply(Eq[1], Eq[2])


if __name__ == '__main__':
    run()
# created on 2022-01-01
