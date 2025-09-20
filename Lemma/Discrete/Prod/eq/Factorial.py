from util import *


@apply
def apply(self):
    (i, j), (j, S[0], i) = self.of(Product[Expr - Expr])

    return Equal(self, factorial(i))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True)
    Eq << apply(Product[i:n](n - i))

    Eq << Eq[-1].this.rhs.apply(Discrete.Factorial.eq.Prod)

    Eq << Eq[-1].this.rhs.apply(Algebra.Prod.limits.subst.Neg, i, n - i)


if __name__ == '__main__':
    run()
# created on 2022-01-15
