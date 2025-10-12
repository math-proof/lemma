from util import *


@apply
def apply(gt, eq):
    a, b = eq.of(Equal)
    x = gt.of(Expr > 0)
    return x > 0, Equal((a / x).expand(), (b / x).expand()).simplify()


@prove
def prove(Eq):
    from Lemma import Algebra, Nat, Nat

    x, y, z = Symbol(integer=True)
    Eq << apply(x > 0, Equal(x + y, z))

    Eq << Algebra.Ne.of.Gt.apply(Eq[0])

    Eq << Nat.EqMulS.of.Eq.apply(Eq[-1], Eq[2])





if __name__ == '__main__':
    run()
# created on 2023-03-26
# updated on 2025-04-19
