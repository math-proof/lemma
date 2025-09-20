from util import *


@apply
def apply(self):
    ((k, n), (S[n], S[k]), S[(-1) ** k]), (S[k], S[0], S[n + 1]) = self.of(Sum[Symbol ** Expr * binomial * Expr])
    return Equal(self, factorial(n) * (-1) ** n)


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra

    n = Symbol(integer=True, nonnegative=True)
    k = Symbol(integer=True)
    Eq << apply(Sum[k:n + 1]((-1) ** k * k ** n * binomial(n, k)))

    Eq << Eq[-1].this.find(Factorial).apply(Discrete.Factorial.eq.Sum.Binom)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum_Mul.eq.Mul_Sum)


if __name__ == '__main__':
    run()
# created on 2023-06-17
