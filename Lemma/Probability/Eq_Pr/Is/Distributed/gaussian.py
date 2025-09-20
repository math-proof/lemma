from util import *


@apply
def apply(self):
    (expr, expr_var), fx = self.of(Equal[Pr[Equal]])
    assert expr_var.is_symbol
    assert not expr_var.is_integer
    assert fx._has(expr_var)

    sigma, mu = fx.of(Expr * Exp)
    sigma *= sqrt(2 * S.Pi)
    sigma = 1 / sigma
    mu *= -sigma ** 2 * 2
    S[expr_var], mu = mu.of((Expr - Expr) ** 2)

    return Distributed(expr, NormalDistribution(mu, sigma ** 2))


@prove
def prove(Eq):
    from Lemma import Probability

    x = Symbol(real=True, random=True)
    μ = Symbol(real=True)
    σ = Symbol(positive=True)
    Eq << apply(Equal(Pr(x), NormalDistribution(μ, σ ** 2)(x.var)))

    Eq << Eq[0].this.rhs.apply(Probability.Distributed.Is.Eq.Pr)




if __name__ == '__main__':
    run()
# created on 2023-04-10
