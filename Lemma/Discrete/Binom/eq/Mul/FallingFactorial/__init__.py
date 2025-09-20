from util import *


@apply
def apply(self):
    n, k = self.of(Binomial)

    return Equal(self, FallingFactorial(n, k) / Factorial(k))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra

    n = Symbol(integer=True, positive=True)
    k = Symbol(domain=Range(n + 1))
    Eq << apply(binomial(n, k))

    Eq << Eq[-1].this.find(FallingFactorial).apply(Discrete.FallingFactorial.eq.Prod)

    Eq << Eq[-1].this.lhs.apply(Discrete.Binom.eq.Mul)

    # Eq << Eq[-1] * Factorial(k)

    Eq << Eq[-1].this.find(Factorial).apply(Discrete.Factorial.eq.Prod)

    Eq << Eq[-1].this.find(Factorial).apply(Discrete.Factorial.eq.Prod)

    i = Eq[-1].rhs.variable
    Eq << Eq[-1].this.lhs.args[0].apply(Algebra.Prod.limits.subst.Neg, i, n - i)

    Eq << Eq[-1].this.find((~Product) ** -1).apply(Algebra.Prod.limits.subst.Neg, i, n - i)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Prod.limits.SDiff)


if __name__ == '__main__':
    run()

# created on 2020-02-28

from . import doit
