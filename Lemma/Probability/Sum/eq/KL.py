from util import *


def extract(Sum, self, order):
    ((prob_lhs, prob_rhs), S[prob_lhs]), *limits = self.of(Sum[Log[Pr / Pr] * Pr])

    return KL(Pr(*prob_lhs), Pr(*prob_rhs))

@apply
def apply(self, order=None):
    return Equal(self, extract(Sum, self, order))


@prove
def prove(Eq):
    from Lemma import Probability

    D = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, integer=True)
    Eq << apply(Sum[x.var](log(Pr[θ](x) / Pr[θ_quote](x)) * Pr[θ](x)))

    Eq << Eq[-1].this.rhs.apply(Probability.KL.eq.Sum)



if __name__ == '__main__':
    run()
# created on 2023-03-26
