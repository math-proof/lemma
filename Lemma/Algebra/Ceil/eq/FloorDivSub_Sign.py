from util import *


@apply
def apply(self):
    n, d = self.of(Ceil[Expr / Expr])
    return Equal(self, (n + d - sign(d)) // d)


@prove
def prove(Eq):
    from Lemma import Algebra

    n = Symbol(integer=True)
    d = Symbol(integer=True, zero=False)
    Eq << apply(ceil(n / d))

    Eq << Eq[-1].this.lhs.apply(Algebra.Ceil.eq.Neg.Floor)

    Eq << Eq[-1].this.rhs.expand()

    Eq << Eq[-1] + (-n // d - 1)

    Eq << Eq[-1].reversed

    Eq << Algebra.Mod.eq.Sub_Mul_Div.apply(-n % d)

    Eq << Algebra.Mod.eq.Sub_Mul_Div.apply((d + n - sign(d)) % d)

    Eq << Eq[-1] + Eq[-2]

    Eq << Eq[-1].this.find(Mod).apply(Algebra.Mod.eq.Sub_Mul_Div)

    Eq << Eq[-1].this.find(Floor).apply(Algebra.Floor.eq.Neg.Ceil)

    Eq << Eq[-1].this.find(Ceil).apply(Algebra.Ceil.eq.One)

    Eq << -Eq[-1] / d









if __name__ == '__main__':
    run()
# created on 2018-05-25
# updated on 2023-05-29
