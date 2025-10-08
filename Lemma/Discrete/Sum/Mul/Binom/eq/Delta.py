from util import *


@apply
def apply(self):
    (a, b), (k, start, n) = self.of(Sum[Expr * (-1) ** Expr])
    n -= 1
    S[k], i = a.of(Binomial * Binomial(n, k))
    assert start in (0, i)
    assert b in (k - i, k + i, n - k, n + k)
    return Equal(self, KroneckerDelta(n, i))


@prove
def prove(Eq):
    from Lemma import Algebra, Discrete, Bool

    k = Symbol(integer=True)
    i = Symbol(integer=True, nonnegative=True, given=False)
    n = Symbol(domain=Range(i, oo))
    Eq << apply(Sum[k:i:n + 1](Binomial(n, k) * (-1) ** (k - i) * Binomial(k, i)))

    m = Symbol(integer=True, nonnegative=True)
    Eq.hypothesis = Eq[0].subs(n, m + i).this.rhs.apply(Algebra.Delta.offset, -i)

    Eq.initial = Eq.hypothesis.subs(i, 0)

    Eq << Eq.initial.this.lhs.apply(Discrete.Sum.Binom.eq.Delta.Zero)

    Eq.induct = Eq.hypothesis.subs(i, i + 1)

    Eq << Eq.induct.this.lhs.apply(Algebra.Sum.eq.Add.by_parts.offset, pivot=slice(1, 2))

    Eq << Eq[-1].this.find(~Binomial - Binomial).apply(Discrete.Binom.eq.Add.Pascal)

    Eq << Eq[-1].this.find(Pow).apply(Algebra.Pow.eq.Mul.split.exponent, simplify=None)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum_Mul.eq.Mul_Sum)

    Eq << Eq[-1].this.find((-1) ** Add).apply(Algebra.Pow.eq.Mul.split.exponent, simplify=None)

    Eq << Eq[-1].this.find(Sum[Mul[~Sum]]).apply(Algebra.Sum_Mul.eq.Mul_Sum)

    Eq << Eq[-1].this.find(Sum[Pow * Binomial]).apply(Discrete.Sum.Binom.eq.Add)

    Eq << Eq[-1].this.find(Sum[Pow * Binomial]).apply(Discrete.Sum.Binom.eq.Add)

    Eq << Eq[-1].this.find(Sum).expr.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Pow * Pow).args[:2].apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(Algebra.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.eq.Sub.unshift)

    Eq << Eq[-1].this.find(Sum[Binomial]).apply(Algebra.Sum.eq.Sub.unshift)

    Eq << Eq[-1].this.find(Mul).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Sum[Binomial]).apply(Algebra.Sum.limits.subst.offset, i)

    Eq << Eq[-1].this.find(Sum[Binomial]).apply(Discrete.Sum.Binom.eq.Binom)

    Eq << Imply(Eq.hypothesis, Eq.induct, plausible=True)

    Eq << Bool.Eq.of.Eq.All_Imp.apply(Eq.initial, Eq[-1], i, 0)

    Eq << Eq.hypothesis.subs(m, n - i)

    Eq << Eq[-1].this.rhs.apply(Algebra.Delta.offset, i)





if __name__ == '__main__':
    run()
# created on 2023-06-17
# updated on 2023-08-27
