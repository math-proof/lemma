from util import *


@apply
def apply(self):
    n, d = self.of(Ceil[Expr / Expr])
    return Equal(self, (n + d - sign(d)) // d)


@prove
def prove(Eq):
    from Lemma import Int, Nat

    n = Symbol(integer=True)
    d = Symbol(integer=True, zero=False)
    Eq << apply(ceil(n / d))

    Eq << Eq[-1].this.lhs.apply(Int.Ceil.eq.NegFloorNeg)

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1] + (-n // d - 1)

    Eq << Eq[-1].reversed

    Eq << Nat.Mod.eq.Sub_Mul_FloorDiv.apply(-n % d)

    Eq << Nat.Mod.eq.Sub_Mul_FloorDiv.apply((d + n - sign(d)) % d)

    Eq << Eq[-1] + Eq[-2]

    Eq << Eq[-1].this.find(Mod).apply(Nat.Mod.eq.Sub_Mul_FloorDiv)

    Eq << Eq[-1].this.find(Floor).apply(Int.Floor.eq.NegCeilNeg)

    Eq << Eq[-1].this.find(Ceil).apply(Int.CeilDivSign.eq.One.of.Ne_0)

    Eq << -Eq[-1] / d









if __name__ == '__main__':
    run()
# created on 2018-05-25
# updated on 2023-05-29
