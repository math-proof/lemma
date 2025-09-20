from util import *


@apply
def apply(self):
    ((n, k), (S[k], S[3]), (x, S[k])), (S[k], a, S[n + 1]) = self.of(Sum[Binomial * Pow * Pow])
    assert a in (0, 1)
    return Equal(self, RisingFactorial(n * x, 3) * (x + 1) ** (n - 3) - n * x * (x + 1) ** (n - 2))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete

    x, k = Symbol(integer=True)
    n = Symbol(integer=True, positive=True)
    Eq << apply(Sum[k:n + 1](Binomial(n, k) * x ** k * k ** 3))

    Eq << Eq[0].this.lhs.apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[-1].this.lhs().find(Binomial).apply(Discrete.Binom.eq.Div.Binom)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.subst.offset, 1)

    Eq << Eq[-1].this.lhs.find(Pow).apply(Algebra.Pow.eq.Mul.split.exponent)

    Eq << Eq[-1].this.find(Add ** 2).apply(Algebra.Pow.eq.Add)

    Eq << Eq[-1].this.find(Sum).expr.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Sum[Mul[Symbol]]).apply(Algebra.Sum.eq.Sub.unshift)

    Eq << Eq[-1].this.find(Sum[Mul[Symbol]]).apply(Discrete.Sum.Binom.eq.Mul.Newton)

    Eq << Eq[-1].this.find(Sum).apply(Discrete.Sum.Binom.eq.Pow.Newton)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Sub.unshift)

    Eq << Eq[-1].this.lhs.apply(Algebra.Add.collect, factor=x)

    Eq << Eq[-1].this.find(Sum).apply(Discrete.Sum.Binom.eq.Mul.Newton.deux)

    Eq << Algebra.Eq.given.Eq_0.apply(Eq[-1])

    Eq << Eq[-1].this.find(Mul + Mul).apply(Algebra.Add.collect, factor=(x + 1) ** (n - 3))

    Eq << Eq[-1].this.find(1 + ~Mul).expand()

    Eq << Eq[-1].this.lhs.args[1].expand()





if __name__ == '__main__':
    run()
# created on 2021-11-26
# updated on 2023-04-12
