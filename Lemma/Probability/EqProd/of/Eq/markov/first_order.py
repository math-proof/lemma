from util import *


@apply
def apply(eq, n):
    ((s, k), S[s[:k].as_boolean()]), (S[s[k]], S[s[k - 1].as_boolean()]) = eq.of(Equal[Conditioned[Indexed], Conditioned])
    t, = k.free_symbols
    start = k - t
    stop = n + start
    assert s.is_random
    return Equal(Pr(s[1:n + 1] | s[0]),
                 Product[t:start + 1:stop + 1](Pr(s[k] | s[k - 1])))


@prove
def prove(Eq):
    from Lemma import Probability, Algebra

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True)  # states / observation
    k = Symbol(integer=True)  # time step counter
    n = Symbol(integer=True, positive=True)  # total time step
    Eq << apply(Equal(s[k] | s[:k], s[k] | s[k - 1]), n)

    Eq << Probability.EqPr.of.Eq.apply(Eq[0], simplify=False)

    Eq << Algebra.EqProd.of.Eq.apply(Eq[-1], (k, 1, n + 1))

    Eq << Eq[-1].this.find(Pr).apply(Probability.Pr.eq.Div.Pr.bayes)

    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.Eq.Is.Eq.concat)

    Eq << Eq[-1].this.find(Equal[Sliced]).apply(Algebra.Eq.Is.And.Eq.split, 1)

    Eq << Eq[1].this.lhs.apply(Probability.Pr.eq.Div.Pr.bayes)


if __name__ == '__main__':
    run()
# created on 2023-03-30
