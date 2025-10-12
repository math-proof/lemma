from util import *


@apply
def apply(self):
    n = self.of(Factorial)
    assert n > 0
    return Equal(self, n * factorial(n - 1))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Finset

    n = Symbol(integer=True, positive=True)
    Eq << apply(factorial(n))

    Eq << Eq[0].this.find(factorial).apply(Discrete.Factorial.eq.Prod)

    Eq << Eq[-1].this.find(factorial).apply(Discrete.Factorial.eq.Prod)

    Eq << Eq[-1].this.lhs.apply(Finset.Prod.eq.MulProdS, cond={n})


if __name__ == '__main__':
    run()
# created on 2020-08-06
del Factorial2
from . import Factorial2
