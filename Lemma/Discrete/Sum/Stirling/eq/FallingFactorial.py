from util import *


@apply
def apply(self):
    ((x, k), (n, S[k]), exp), (k, S[0], S[n + 1]) = self.of(Sum[Pow * Stirling1 * (-1) ** Expr])
    assert exp in (n + k, n - k)
    return Equal(self, FallingFactorial(x, n))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Finset

    k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    x = Symbol(real=True)
    Eq << apply(Sum[k:n + 1](x ** k * Stirling1(n, k) * (-1) ** (n - k)))

    Eq << Discrete.RisingFactorial.eq.Sum.Stirling.apply(RisingFactorial(-x, n), k)

    Eq << Eq[-1].this.lhs.apply(Discrete.RisingFactorial.eq.Mul.FallingFactorial)

    Eq << Eq[-1].this.rhs.find(Pow).apply(Algebra.Pow.eq.Mul.split.base)

    Eq << Eq[-1] * (-1) ** n

    Eq << Eq[-1].this.rhs.apply(Finset.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].reversed




if __name__ == '__main__':
    run()
# created on 2023-08-26
