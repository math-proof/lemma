from util import *


@apply
def apply(self):
    (i, j), (S[j], S[0], i), (S[i], S[0], n) = self.of(Sum[Expr - Expr])
    return Equal(self, Binomial(n + 1, 3))


@prove
def prove(Eq):
    from Lemma import Discrete

    n = Symbol(domain=Range(2, oo))
    i, j = Symbol(integer=True)
    Eq << apply(Sum[j:i, i:n]((i - j)))

    t = Symbol(integer=True, nonnegative=True)
    Eq << Discrete.Sum.Binom.eq.Binom.Sign.apply(Sum[j:i, i:n](Binomial(i - j, t)))

    Eq << Eq[-1].subs(t, 1)





if __name__ == '__main__':
    run()
# created on 2023-10-21
# updated on 2023-10-22
