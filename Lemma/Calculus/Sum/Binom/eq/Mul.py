from util import *


@apply
def apply(self):
    ((r, n), S[n], (x, S[n])), (S[n], S[0], S[oo]) = self.of(Sum[Binomial * Symbol * Pow])

    return Equal(self, r * x * (1 + x) ** (r - 1))


@prove
def prove(Eq):
    from Lemma import Calculus, Algebra

    x, r = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(Sum[n:oo](binomial(r, n) * n * x ** n))

    Eq << Calculus.Pow.eq.Sum.Binom.apply((1 + x) ** r, n)

    Eq << Calculus.EqGrad.of.Eq.apply(Eq[-1], (x,))

    Eq << Eq[-1].this.lhs.doit()

    Eq << Eq[-1].this.rhs.doit()

    Eq << Eq[-1] * x

    Eq << Eq[-1].this.rhs.apply(Algebra.Mul_Sum.eq.Sum_Mul).reversed
    Eq << Eq[-1].this.rhs.powsimp()





if __name__ == '__main__':
    run()
# created on 2021-11-25
