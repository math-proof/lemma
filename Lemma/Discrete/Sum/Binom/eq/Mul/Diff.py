from util import *


@apply
def apply(self):
    (jk, (n, ki), fk), (k, i, S[n + i + 1]) = self.of(Sum[(-1) ** Add * Binomial * Expr])
    if n in jk:
        jk = [*jk]
        jk.remove(n)

        _k, j = jk
        if _k != k:
            _k, j = j, _k
            assert _k == k

        exponent = i - j
    else:
        _k, j = jk
        if _k != k:
            _k, j = j, _k
            assert _k == k
        exponent = n + i - j

    assert i == k - ki


    return Equal(self, (-1) ** exponent * Difference(fk, (k, n)))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Finset

    n = Symbol(integer=True, positive=True)
    i = Symbol(integer=True, given=True)
    k, j = Symbol(integer=True)
    f = Function(real=True)
    Eq << apply(Sum[k:i:n + i + 1]((-1) ** (j - k) * Binomial(n, k - i) * f(k)))

    Eq << Eq[0].this.lhs.apply(Algebra.Sum.limits.subst.offset, i)

    Eq << Eq[-1] * (-1) ** (n - i - j)

    Eq << Eq[-1].this.lhs.apply(Finset.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.lhs.apply(Discrete.Sum.Binom.eq.Diff, var=k)





if __name__ == '__main__':
    run()
# created on 2021-11-26
