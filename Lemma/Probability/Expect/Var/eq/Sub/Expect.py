from util import *


@apply
def apply(self):
    ((expr, given), *limits_v), *limits_e = self.of(Expectation[Variance[Conditioned]])
    x, x_var = given.of(Equal)
    [S[x]], = limits_e
    assert x.is_probable
    return Equal(self,
                 Expectation(expr.outer_product(), *limits_v) - Expectation(Expectation(expr | given, *limits_v).outer_product(), *limits_e))

@prove
def prove(Eq):
    from Lemma import Probability

    n = Symbol(integer=True, positive=True)
    y = Symbol(real=True, random=True, shape=(n,))
    x = Symbol(real=True, probable=True)
    Eq << apply(Expectation(Variance(y | x.surrogate)))

    Eq << Eq[0].this.find(Variance).apply(Probability.Var.eq.Sub.Expect)

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Add)

    Eq << Eq[-1].this.find(Expectation[Mul]).apply(Probability.Expect.eq.Mul)

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.law_of_total_expectation)




if __name__ == '__main__':
    run()
# created on 2023-04-09
# updated on 2023-04-14
