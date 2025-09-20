from util import *


@apply
def apply(self):
    args = self.of(Mul)
    k = len(args)
    n = max(args)

    for i in range(k):
        assert n - i in args

    return Equal(self, Binomial(n, k) * Factorial(k))


@prove
def prove(Eq):
    from Lemma import Discrete

    n = Symbol(integer=True, positive=True)
    k, i = Symbol(integer=True)
    Eq << apply(n * (n - 1) * (n - 2))

    Eq << Eq[0].this.find(Binomial).apply(Discrete.Binom.eq.Mul.FallingFactorial.doit)


if __name__ == '__main__':
    run()
# created on 2023-10-12
