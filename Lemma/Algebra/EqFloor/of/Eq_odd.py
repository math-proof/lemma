from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 1])
    return Equal(n // 2, (n - 1) / 2)


@prove
def prove(Eq):
    from Lemma import Algebra, Bool, Rat, Nat

    # n = q * d + r
    n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 1))

    Eq << Nat.Any_Eq_AddMul2.of.Odd.apply(Eq[0])

    Eq << Eq[-1].this.expr.apply(Nat.Div.of.Eq, 2, simplify=None)

    Eq << Eq[-1].this.expr.apply(Rat.Floor.of.Eq, ret=0)

    Eq << Eq[-1].this.expr.args[0] - S.One / 2

    Eq << Eq[-1].this.expr.apply(Bool.Eq.of.Eq.Eq)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2019-10-12
