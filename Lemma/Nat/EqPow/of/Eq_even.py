from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 0])
    return Equal((-1) ** n, 1)


@prove
def prove(Eq):
    from Lemma import Nat
#     n = q * d + r
    n = Symbol(integer=True)

    Eq << apply(Equal(n % 2, 0))

    Eq << Nat.Any_Eq_Mul2.of.Even.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(Nat.Pow.of.Eq, base=-1)


if __name__ == '__main__':
    run()

# created on 2019-10-10
