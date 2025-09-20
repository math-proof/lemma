from util import *


@apply
def apply(self):
    ((r, n), (x, S[n])), (S[n], S[0], S[oo]) = self.of(Sum[Binomial * Pow])

    return Equal(self, (1 + x) ** r)


@prove
def prove(Eq):
    from Lemma import Calculus

    x, r = Symbol(real=True)
    n = Symbol(integer=True)
    Eq << apply(Sum[n:oo](Binomial(r, n) * x ** n))

    Eq << Eq[-1].this.rhs.apply(Calculus.Pow.eq.Sum.Binom)


if __name__ == '__main__':
    run()
# created on 2021-11-25
