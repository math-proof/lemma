from util import *


def extract(Sum, self):
    args, (x_var, *_) = self.of(Sum[Pr[Conditioned]])
    if args[-1].is_Tuple:
        args, *weights = args

    cond, given = args
    x, S[x_var] = cond.of(Equal)
    return 1

@apply
def apply(self):
    return Equal(self, extract(Sum, self))


@prove
def prove(Eq):
    from Lemma import Probability

    x, y = Symbol(integer=True, random=True)
    Eq << apply(Sum[x.var](Pr(x | y)))

    Eq << Eq[-1].this.lhs.expr.apply(Probability.Pr.eq.Div.Pr.bayes)

    Eq << Eq[-1].this.find(Sum).apply(Probability.Sum.eq.Pr)



if __name__ == '__main__':
    run()
# created on 2021-07-18
# updated on 2023-03-25
