from util import *


@apply
def apply(self):
    ((n, k), (S[k], S[2]), (x, S[k])), (S[k], a, S[n + 1]) = self.of(Sum[Binomial * Pow * Pow])
    assert a in (0, 1)
    return Equal(self, n * x * (n * x + 1) * (x + 1) ** (n - 2))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Finset

    x, k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Sum[k:n + 1](Binomial(n, k) * x ** k * k ** 2))

    Eq << Eq[0].this.lhs.apply(Algebra.Sum.eq.Add.shift)
    Eq << Eq[-1].this.lhs().find(Binomial).apply(Discrete.Binom.eq.Div.Binom)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.subst.offset, 1)

    Eq << Eq[-1].this.lhs.find(Pow).apply(Algebra.Pow.eq.Mul.split.exponent)

    Eq << Eq[-1].this.find(Sum).expr.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Sum).apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Sum[Mul[Symbol]]).apply(Algebra.Sum.eq.Sub.unshift)

    Eq << Eq[-1].this.find(Sum[Mul[Symbol]]).apply(Discrete.Sum.Binom.eq.Mul.Newton)

    Eq << Eq[-1].this.find(Sum).apply(Discrete.Sum.Binom.eq.Pow.Newton)

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.collect, factor=x)

    Eq << Eq[-1].this.find(Add[Pow]).apply(Algebra.Add.collect, factor=(x + 1) ** (n - 2))

    Eq << Eq[-1].this.find(1 + ~Mul).expand()




if __name__ == '__main__':
    run()
# created on 2021-11-26
# updated on 2023-04-12
