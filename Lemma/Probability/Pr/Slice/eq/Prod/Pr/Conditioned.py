from util import *


@apply
def apply(self, k=None):
    (s, (S[0], n)), S[s[:n].var] = self.of(Pr[Equal[Sliced]])
    return Equal(self, Product[k:n](Pr(s[k] | s[:k])), evaluate=False)


@prove
def prove(Eq):
    from Lemma import Probability

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True)  # states / observation
    k = Symbol(integer=True)  # time step counter
    n = Symbol(integer=True, nonnegative=True)  # total time step
    Eq << apply(Pr(s[:n]), k)

    Eq << Eq[0].this.rhs.apply(Probability.Prod.Pr.Conditioned.eq.Pr.Slice)

    # https://arxiv.org/pdf/1909.08593.pdf# 2



if __name__ == '__main__':
    run()
# created on 2023-04-08
