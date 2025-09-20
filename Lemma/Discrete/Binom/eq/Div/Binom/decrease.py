from util import *


@apply
def apply(self):
    n, k = self.of(Binomial)
    return Equal(self, Binomial(n - 1, k) / (n - k) * n)


@prove
def prove(Eq):
    from Lemma import Discrete

    n = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(n))
    Eq << apply(Binomial(n, k))

    Eq << Eq[-1].this.find(binomial).apply(Discrete.Binom.eq.Mul)

    Eq << Eq[-1].this.find(binomial).apply(Discrete.Binom.eq.Mul)

    Eq << Eq[-1].this.find(Factorial).apply(Discrete.Factorial.eq.Mul)


    Eq << Eq[-1].this.find(Factorial).apply(Discrete.Factorial.eq.Mul)




if __name__ == '__main__':
    run()
# created on 2020-10-07
# updated on 2023-06-03
