from util import *


from sympy.functions.combinatorial.numbers import Stirling

@apply
def apply(self):
    ((i, n), (k, S[i]), S[i + k]), (i, S[0], S[k + 1]) = self.of(Sum[Pow * Binomial * (-1) ** Expr])

    return Equal(self, factorial(k) * Stirling(n, k))


@prove
def prove(Eq):
    from Lemma import Discrete

    n, k = Symbol(integer=True, nonnegative=True)
    i = Symbol(integer=True)
    Eq << apply(Sum[i:k + 1]((-1) ** (k - i) * binomial(k, i) * i ** n))

    Eq << Eq[0].this.find(Stirling).apply(Discrete.Stirling.eq.Mul.Sum)




if __name__ == '__main__':
    run()
# created on 2022-01-18
# updated on 2023-08-27
