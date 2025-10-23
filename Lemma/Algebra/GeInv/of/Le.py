from util import *


@apply
def apply(ge):
    x, a = ge.of(LessEqual)
    assert x > 0

    return GreaterEqual(1 / x, 1 / a)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat, Nat

    x = Symbol(real=True, positive=True)
    a = Symbol(real=True)
    Eq << apply(x <= a)

    Eq << Algebra.Gt_0.of.Le.apply(Eq[0])

    Eq << Algebra.Div.gt.Zero.of.Gt_0.apply(Eq[-1])

    Eq << Nat.LeMul.of.Gt_0.Le.apply(Eq[-1], Eq[0])

    Eq << Eq[1] * x
    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-10-31
