from util import *


@apply
def apply(self):
    n, k = self.of(Binomial)
    return Equal(self, binomial(n, n - k))


@prove
def prove(Eq):
    from Lemma import Discrete

    n, k = Symbol(integer=True)
    Eq << apply(Binomial(n, k))

    Eq << Eq[-1].this.lhs.apply(Discrete.Binom.eq.Mul)

    Eq << Eq[-1].this.rhs.apply(Discrete.Binom.eq.Mul)





if __name__ == '__main__':
    run()
# created on 2020-09-28
# updated on 2021-11-26