from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 0])
    return Equal(n // 2, n / 2)


@prove
def prove(Eq):
    from Lemma import Bool, Rat, Nat

    # n = q * d + r
    n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 0))

    Eq << Nat.Any_Eq_Mul2.of.Even.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(Nat.Div.of.Eq, 2, simplify=None)

    Eq << Eq[-1].this.expr.apply(Rat.Floor.of.Eq, ret=0)

    Eq << Eq[-1].this.expr.apply(Bool.Eq.of.Eq.Eq)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-10-10
