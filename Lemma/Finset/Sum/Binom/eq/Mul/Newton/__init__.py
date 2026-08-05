from util import *


@apply
def apply(self):
    ((n, k), S[k], (x, S[k])), (S[k], a, S[n + 1]) = self.of(Sum[Binomial * Symbol * Pow])
    assert a in (0, 1)
    return Equal(self, n * (x + 1) ** (n - 1) * x)


@prove
def prove(Eq):
    from Lemma import Algebra, Finset

    x, k = Symbol(integer=True)
    n = Symbol(integer=True, nonnegative=True)
    Eq << apply(Sum[k:n + 1](Binomial(n, k) * x ** k * k))

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[-1].this.lhs().find(Binomial).apply(Finset.Binom.eq.Div.Binom)

    Eq << Eq[-1].this.find(Sum).apply(Finset.SumIco.eq.Sum_UFnAdd, 1)

    Eq << Eq[-1].this.lhs.find(Pow).apply(Algebra.Pow.eq.Mul.split.exponent)

    Eq << Eq[-1].this.find(Sum).apply(Finset.Sum.Binom.eq.Pow.Newton)





if __name__ == '__main__':
    run()
# created on 2021-11-25
# updated on 2023-04-12
from . import quatre
from . import deux
from . import trois
