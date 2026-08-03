from util import *


@apply
def apply(given):
    n = given.of(Equal[Expr % 2, 1])
    return Equal((n + 1) % 2, 0)


@prove
def prove(Eq):
    from Lemma import Algebra, Nat

    n = Symbol(integer=True)
    Eq << apply(Equal(n % 2, 1))

    Eq << Eq[1].lhs.this.apply(Nat.Mod.eq.Sub_Mul_FloorDiv)

    Eq << Eq[0].this.lhs.apply(Nat.Mod.eq.Sub_Mul_FloorDiv)

    Eq << Algebra.Eq.of.Eq.transport.apply(Eq[-1])

    Eq << Eq[-3].this.rhs.subs(Eq[-1])



if __name__ == '__main__':
    run()
# created on 2023-05-30
