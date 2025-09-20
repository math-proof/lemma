from util import *


@apply
def apply(self):
    ((ijk, i), fk), (k, h, j1), (j, S[h], n) = self.of(Sum[Binomial * Expr])
    S[j + 1] = j1
    S[i + j] = ijk + k
    assert fk._has(k)
    assert not fk._has(j)
    return Equal(self, Sum[k:h:n](Binomial(n - k + i, i + 1) * fk))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete

    n = Symbol(integer=True, positive=True)
    k, i, j, h = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[k:h:j + 1, j:h:n](Binomial(i + j - k, i) * f(k)))

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.swap.intlimit)

    Eq << Eq[-1].this.lhs.apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.lhs.find(Sum).apply(Algebra.Sum.limits.subst.offset, offset=k)

    Eq << Eq[-1].this.lhs.find(Sum).apply(Discrete.Sum.Binom.eq.Binom)




if __name__ == '__main__':
    run()
# created on 2023-06-03
