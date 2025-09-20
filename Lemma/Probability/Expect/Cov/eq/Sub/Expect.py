from util import *


@apply
def apply(self):
    ((x, given), (y, S[given])), *limits_e = self.of(Expectation[Covariance[Conditioned, Conditioned]])
    vars_given= set()
    if given.is_And:
        conds = given.args
    else:
        conds = [given]

    for eq in conds:
        z, z_var = eq.of(Equal)
        vars_given.add(z)

    for z, *ab in limits_e:
        assert z in vars_given

    return Equal(self,
                 Expectation(x.outer_product(y)) - Expectation(Expectation(x | given).outer_product(Expectation(y | given)), *limits_e))

@prove
def prove(Eq):
    from Lemma import Probability

    n = Symbol(integer=True, positive=True)
    x, y = Symbol(real=True, random=True, shape=(n,))
    z = Symbol(real=True, probable=True)
    Eq << apply(Expectation(Covariance(x, y, given=z.surrogate)))

    Eq << Eq[0].this.find(Covariance).apply(Probability.Cov.eq.Sub.Expect)

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Add)

    Eq << Eq[-1].this.find(Expectation[Mul]).apply(Probability.Expect.eq.Mul)

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.law_of_total_expectation)




if __name__ == '__main__':
    run()
# created on 2023-04-09
# updated on 2023-04-14
