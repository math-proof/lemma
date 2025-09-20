from util import *


@apply
def apply(self):
    base, β = self.of(Expr ** (1 / Symbol))
    M, (m, S[-β]), (n, α) = base.of(Symbol * Pow * Pow)
    α = -α
    return Equal(self, (M / n ** α) ** (1 / β) / m)


@prove
def prove(Eq):
    from Lemma import Algebra

    m, n = Symbol(integer=True, positive=True)
    # m indicates batch-size, n indicates seq-length
    # α indicates seq-length-exponent
    # β indicates batch-size-exponent
    # M indicates maximum batch-size-memory
    α, β, M = Symbol(real=True, positive=True)
    Eq << apply((M / (n ** α * m ** β)) ** (1 / β))

    Eq << Eq[0].this.lhs.apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Eq[-1].this.rhs.apply(Algebra.Pow.eq.Mul.split.base)


if __name__ == '__main__':
    run()
# created on 2024-07-06
