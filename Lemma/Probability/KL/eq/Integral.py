from util import *


@apply
def apply(self, order=None):
    from Lemma.Probability.KL.eq.Sum import extract
    return Equal(self, extract(Integral, self, order))


@prove
def prove(Eq):
    from Lemma import Probability

    D = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True)
    Eq << apply(KL(Pr[θ](Equal(x, x.var)), Pr[θ_quote](Equal(x, x.var))))

    Eq << Eq[-1].this.find(KL).apply(Probability.KL.eq.Expect)
    Eq << Eq[-1].this.find(Expectation).apply(Probability.Expect.eq.Integral)


if __name__ == '__main__':
    run()
# created on 2023-03-25
