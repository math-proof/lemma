from util import *


@apply
def apply(self):
    ((x, given), *limits_x), ((y, S[given]), *limits_y) = self.of(Covariance[Expectation[Conditioned], Expectation[Conditioned]])
    return Equal(self,
                 Expectation(Expectation(x | given, *limits_x).outer_product(Expectation(y | given, *limits_y))) - Expectation(x, *limits_x).outer_product(Expectation(y, *limits_y)))

@prove
def prove(Eq):
    from Lemma import Probability

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, random=True, shape=(n,))
    z = Symbol(real=True, probable=True)
    Eq << apply(Covariance(Expectation(x | z.surrogate), Expectation(y | z.surrogate)))

    Eq << Eq[0].this.lhs.apply(Probability.Cov.eq.Sub.Expect)

    Eq << Eq[-1].this.find(Expectation[Expectation]).apply(Probability.Expect.law_of_total_expectation)

    Eq << Eq[-1].this.find(Expectation[Expectation]).apply(Probability.Expect.law_of_total_expectation)




if __name__ == '__main__':
    run()
# created on 2023-04-09
# updated on 2023-04-14
