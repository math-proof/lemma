from util import *


@apply
def apply(eq_expect, eq_var, k):
    (x, *limits), μ = eq_expect.of(Equal[Expectation])
    (S[x], *S[limits]), D = eq_var.of(Equal[Variance])
    σ = sqrt(D)
    assert k > 0
    return Pr(Abs(x - μ) >= k * σ) <= 1 / k ** 2


@prove
def prove(Eq):
    from Lemma import Probability, Algebra

    x = Symbol(real=True, random=True)
    k = Symbol(positive=True)
    μ = Symbol(real=True)
    σ = Symbol(positive=True)
    Eq << apply(Equal(Expectation(x), μ), Equal(Variance(x), σ ** 2), k)

    Eq << Probability.PrGeAbs.le.DivExpectAbs.Markov_Inequality.apply((x - μ) ** 2, (k * σ) ** 2)

    Eq << Eq[1].this.lhs.apply(Probability.Var.eq.Expect)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Eq[-3].subs(Eq[-1])

    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge.Is.Ge_0)

    Eq << Eq[-1].this.find(GreaterEqual).lhs.apply(Algebra.Sub.Square.eq.Mul)

    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge_0.Is.Or.split.Mul)

    Eq << Eq[-1].this.find(LessEqual) - k * σ

    Eq << Eq[-1].this.find(LessEqual) + k * σ

    Eq << Eq[-1].this.find(GreaterEqual) - k * σ

    Eq << Eq[-1].this.find(GreaterEqual) + k * σ

    Eq << Eq[-1].this.find(Or).apply(Algebra.Or.Is.GeAbs)




if __name__ == '__main__':
    run()
# created on 2023-04-18
# updated on 2023-05-18
