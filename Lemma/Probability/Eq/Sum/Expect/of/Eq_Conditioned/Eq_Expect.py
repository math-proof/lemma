from util import *


@apply
def apply(eq_conditioned, eq_expect, j=None, n=None):
    ((x, k), S[x[:k].as_boolean()]), S[x[k]] = eq_conditioned.of(Equal[Conditioned[Indexed]])
    (S[x[k]], (S[x[k]],)), μ = eq_expect.of(Equal[Expectation])
    if n is None:
        n = k
    assert n > 1
    if j is None:
        j = eq_expect.generate_var(integer=True, var='j')
    return Equal(Sum[j:k, k:n](Expectation(x[j] * x[k])), Binomial(n, 2) * μ ** 2)


@prove
def prove(Eq):
    from Lemma import Discrete, Probability, Algebra, Finset, Vector

    x = Symbol(real=True, shape=(oo,), random=True)
    μ = Symbol(real=True)
    ε, σ = Symbol(positive=True)
    k, j = Symbol(integer=True)
    n = Symbol(domain=Range(2, oo))
    Eq << apply(Equal(x[k] | x[:k], x[k]), Equal(Expectation(x[k]), μ), j, n)

    Eq << Eq[-1].this.find(Binomial).apply(Discrete.Binom.eq.Div.Binom)

    Eq << Probability.Var.eq.Sum.of.Eq_Conditioned.apply(Eq[0], n)

    Eq << Eq[-1].this.find(ReducedSum).apply(Vector.Sum.eq.Sum_Get, k)

    Eq << Eq[-1].this.lhs.apply(Probability.Var.Sum.eq.Add.Sum, j)

    Eq << Eq[-1].this.find(Covariance).apply(Probability.Cov.eq.Sub.Expect)

    Eq << Eq[-1].this.find(Covariance).apply(Probability.Cov.eq.Sub.Expect)

    Eq << Eq[-1].this.lhs.apply(Finset.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].subs(Eq[1])

    Eq << Eq[-1].this.lhs.apply(Finset.Sum_Mul.eq.Mul_Sum)

    Eq << Eq[-1].subs(Eq[1].subs(k, j))

    Eq << Eq[-1].this.lhs.find(Sum).apply(Algebra.Sum.limits.separate)

    Eq << Eq[-1].this.lhs.find(Sum).apply(Finset.Sum_Mul.eq.Mul_Sum)

    Eq << Eq[-1].this.lhs.find(Sum).apply(Algebra.Sum.eq.Mul.series.arithmetic).reversed

    # https://en.wikipedia.org/wiki/Bessel's_correction



if __name__ == '__main__':
    run()
# created on 2023-10-12
