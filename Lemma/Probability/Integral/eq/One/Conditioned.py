from util import *


@apply
def apply(self):
    from Lemma.Probability.Sum.eq.One.Conditioned import extract
    return Equal(self, extract(Integral, self))


@prove
def prove(Eq):
    from Lemma import Probability

    x, y = Symbol(real=True, random=True)
    Eq << apply(Integral[x.var](Pr(x | y)))

    Eq << Eq[-1].this.lhs.expr.apply(Probability.Pr.eq.Div.Pr.bayes)

    Eq << Eq[-1].this.find(Integral).apply(Probability.Integral.eq.Pr.marginal)





if __name__ == '__main__':
    run()
# created on 2021-07-20
# updated on 2023-03-25
