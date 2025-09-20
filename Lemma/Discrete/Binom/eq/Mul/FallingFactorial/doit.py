from util import *


@apply
def apply(self):
    n, k = self.of(Binomial)
    k = int(k)
    prod = 1
    den = 1
    for i in range(k):
        prod *= (n - i)
        den *= (i + 1)
    return Equal(self, prod / den)


@prove
def prove(Eq):
    from Lemma import Discrete

    n = Symbol(integer=True, positive=True)
    Eq << apply(binomial(n, 3))
    Eq << Eq[-1].this.lhs.apply(Discrete.Binom.eq.Mul.FallingFactorial)


if __name__ == '__main__':
    run()
# created on 2020-02-28
