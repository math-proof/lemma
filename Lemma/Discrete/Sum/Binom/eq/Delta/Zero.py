from util import *


@apply
def apply(self):
    ((n, k), S[k]), (S[k], S[0], S[n + 1]) = self.of(Sum[Binomial * (-1) ** Symbol])
    return Equal(self, KroneckerDelta(n, 0))


@prove
def prove(Eq):
    from Lemma import Discrete

    k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Sum[k:n + 1](Binomial(n, k) * (-1) ** k))
    x = Symbol(real=True)
    Eq << Discrete.Sum.Binom.eq.Pow.Newton.apply(Sum[k:n + 1](Binomial(n, k) * x ** k))
    Eq << Eq[1].subs(x, -1)


if __name__ == '__main__':
    run()
# created on 2023-08-19
