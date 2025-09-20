from util import *


@apply
def apply(self, order=None):
    from Lemma.Probability.Sum.eq.KL import extract
    return Equal(self, extract(Integral, self, order))


@prove
def prove(Eq):
    from Lemma import Probability

    D = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True)
    Eq << apply(Integral[x.var](log(Pr[θ](x) / Pr[θ_quote](x)) * Pr[θ](x)))

    Eq << Eq[-1].this.rhs.apply(Probability.KL.eq.Integral)


if __name__ == '__main__':
    run()
# created on 2023-03-26
