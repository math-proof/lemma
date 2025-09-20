from util import *


@apply
def apply(dist):
    x, (μ, Σ) = dist.of(Distributed[NormalDistribution])
    return Equal(μ, Expectation(x)), Equal(Σ, Variance(x))


@prove(proved=False)
def prove(Eq):
    from Lemma import Probability, Calculus, Algebra

    n = Symbol(integer=True, positive=True)
    x = Symbol(shape=(n,), random=True)
    μ = Symbol(shape=(n,), real=True)
    Σ = Symbol(shape=(n, n), real=True)
    Eq << apply(Distributed(x, NormalDistribution(μ, Σ)))

    Eq << Probability.EqPr.of.Distributed.apply(Eq[0])

    Eq << Expectation(x).this.apply(Probability.Expect.eq.Integral)

    Eq << Eq[-1].subs(Eq[-2])

    Eq << Eq[-1].this.rhs.apply(Calculus.Integral.eq.Mul)

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.limits.offset, μ)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.eq.Add)

    Eq << Eq[-1].this.find(Integral[2]).apply(Calculus.Integral.eq.Mul)

    # https://en.wikipedia.org/wiki/Cholesky_decomposition



if __name__ == '__main__':
    run()
# created on 2023-04-30
# updated on 2023-10-03
