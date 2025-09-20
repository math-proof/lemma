from util import *


@apply
def apply(given):
    args = given.of(Mul > 0)
    args = [arg for arg in args if not arg > 0]
    return Mul(*args) > 0


@prove
def prove(Eq):
    from Lemma import Algebra, Logic

    x = Symbol(real=True)
    a = Symbol(real=True, positive=True)
    Eq << apply(x * a > 0)

    Eq << Logic.Iff.given.Imp.Imp.apply(Eq[0])

    Eq << Eq[-2].this.lhs.apply(Algebra.Gt_0.Mul.of.Gt_0, 1 / a)

    Eq << Eq[-1].this.lhs.apply(Algebra.Gt_0.Mul.of.Gt_0, a)


if __name__ == '__main__':
    run()
# created on 2023-11-05
