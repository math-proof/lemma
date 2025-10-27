from util import *


@apply
def apply(given):
    x = given.of(Expr > 0)
    return sqrt(x) > 0


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    x = Symbol(real=True)
    Eq << apply(x > 0)

    Eq << Nat.Gt_0.of.Gt_0.Gt_0.apply(Eq[1], Eq[1])


if __name__ == '__main__':
    run()
# created on 2023-06-20
