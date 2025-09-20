from util import *


@apply
def apply(self):
    ((ijk, i), fk), (k, j, n), (S[j], h, S[n]) = self.of(Sum[Binomial * Expr])
    S[i + k] = ijk + j
    assert fk._has(k)
    assert not fk._has(j)
    return Equal(self, Sum[k:h:n](Binomial(k + i + 1 - h, i + 1) * fk))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete

    n = Symbol(integer=True, positive=True)
    k, i, j, h = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[k:j:n, j:h:n](Binomial(i + k - j, i) * f(k)))

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.swap.intlimit)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.lhs.find(Sum).apply(Algebra.Sum.limits.subst.Neg, j, k - j)

    Eq << Eq[-1].this.lhs.find(Sum).apply(Discrete.Sum.Binom.eq.Binom)




if __name__ == '__main__':
    run()
# created on 2023-06-03
