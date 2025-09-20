from util import *


@apply
def apply(self):
    ((n, k), S[k]), (S[k], i, m) = self.of(Sum[Binomial * (-1) ** Symbol])
    m -= 1
    return Equal(self, Binomial(n - 1, m) * (-1) ** m + Binomial(n - 1, i - 1) * (-1) ** i)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra

    m, n, i = Symbol(integer=True, nonnegative=True)
    k = Symbol(integer=True)
    Eq << apply(Sum[k:i:m + 1](Binomial(n, k) * (-1) ** k))

    Eq << Eq[0].this.find(Binomial).apply(Discrete.Binom.eq.Add.Pascal)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.lhs.expr.args[1].apply(Algebra.Mul.Neg)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Sub.telescope)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.Neg, 1)





if __name__ == '__main__':
    run()
# created on 2023-04-21
# updated on 2023-08-19
