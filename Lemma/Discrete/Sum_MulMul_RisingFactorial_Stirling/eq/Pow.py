from util import *


@apply
def apply(self):
    ((x, k), (n, S[k]), exp), (k, S[0], S[n + 1]) = self.of(Sum[RisingFactorial * Stirling * (-1) ** Expr])
    assert exp in (n + k, n - k)
    return Equal(self, x ** n)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Finset

    k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    x = Symbol(real=True)
    Eq << apply(Sum[k:n + 1](RisingFactorial(x, k) * Stirling(n, k) * (-1) ** (n - k)))

    Eq << Discrete.Pow.eq.Sum.Stirling.FallingFactorial.apply((-x) ** n, k)

    Eq << Eq[-1].this.find(FallingFactorial).apply(Discrete.FallingFactorial.eq.Mul.RisingFactorial)

    Eq << Eq[-1] * (-1) ** n

    Eq << Eq[-1].this.rhs.apply(Finset.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Pow.Mul.base)

    Eq << Eq[-1].reversed


if __name__ == '__main__':
    run()
# created on 2023-08-26
