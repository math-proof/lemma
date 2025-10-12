from util import *


@apply
def apply(self):
    ((n, k), (fx, (x, S[k]))), (S[k], S[0], S[n + 1]) = self.of(Sum[Binomial * Difference])
    return Equal(self, fx._subs(x, x + n))


@prove
def prove(Eq):
    from Lemma import Discrete, Algebra, Finset

    n = Symbol(integer=True, positive=True)
    k = Symbol(integer=True)
    f = Function(real=True)
    x = Symbol(real=True)
    Eq << apply(Sum[k:n + 1](Binomial(n, k) * Difference(f(x), (x, k))))

    Eq << Eq[0].this.find(Difference).apply(Discrete.Diff.eq.Sum.Binom)

    Eq << Eq[-1].this.lhs.expr.apply(Finset.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.swap.intlimit)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.lhs.find(Sum).apply(Discrete.Sum.Mul.Binom.eq.Delta)


if __name__ == '__main__':
    run()
# created on 2023-08-19
# updated on 2023-08-20
