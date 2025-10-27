from util import *


@apply
def apply(eq):
    ((s, k), S[s[:k].as_boolean()]), (S[s[k]], S[s[k - 1].as_boolean()]) = eq.of(Equal[Conditioned[Indexed], Conditioned])
    assert s.is_random
    return Equal(Pr(s[k + 1] | s[k]) * Pr(s[1:k + 1] | s[0]),
                 Pr(s[1:k + 2] | s[0]))


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Bool, Rat

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True)  # states / observation
    k = Symbol(integer=True)  # time step counter
    Eq << apply(Equal(s[k] | s[:k], s[k] | s[k - 1]))

    Eq << Rat.Ne_0.of.Div1.gt.Zero.apply(Eq[0])

    Eq << Bool.Cond.of.And.apply(Eq[-1])

    Eq <<= Eq[-1].subs(k, 1), Eq[-1].subs(k, k + 1)

    Eq << Probability.EqProd.of.Eq.markov.first_order.apply(Eq[0], k)

    Eq << Eq[1].subs(Eq[-1])

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1], None)

    Eq << Eq[-1].this.lhs.apply(Algebra.Mul.eq.Prod.limits.push)

    Eq << Probability.EqProd.of.Eq.markov.first_order.apply(Eq[0], k + 1)

    Eq << Eq[-1].reversed





if __name__ == '__main__':
    run()
# created on 2023-03-30
# updated on 2023-05-20
