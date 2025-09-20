from util import *


@apply
def apply(eq, k=None, π=None):
    ((r, t), (((a, (S[0], S[t])), S[a[:t].var]), ((s, (S[0], S[t])), S[s[:t].var]))), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced] & Equal[Sliced]]])

    if k is None:
        k = Symbol(integer=True) # time counter

    assert s.is_random and r.is_random and a.is_random

    st = s[t].as_boolean(surrogate=True)
    at = a[t].as_boolean(surrogate=True)
    prob = Pr[a:π](at, given=st)

    return Equal(Expectation[r[t:], a[t]:π, s[t]](Derivative[π](log(prob)) * ReducedSum(r[t:])),
                 Expectation[a[t]:π, s[t]](Derivative[π](log(prob)) * Expectation[r[t:], a:π](ReducedSum(r[t:]) | at & st)))


@prove
def prove(Eq):
    from Lemma import Probability

    b, D = Symbol(integer=True, positive=True)
    π = Symbol(real=True, shape=(D,))
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t, k = Symbol(integer=True) # time counter
    Eq << apply(
        Equal(r[t] | a[:t] & s[:t], r[t]), # history-irrelevant conditional independence assumption
        k, π)

    Eq << Eq[-1].lhs.this.apply(Probability.Expect.law_of_iterated_expectation, a[:t + 1], s[:t + 1])

    Eq << Eq[-1].this.rhs.find(Expectation[Conditioned]).apply(Probability.Expect.eq.Mul)

    Eq << Eq[-1].this.rhs.find(Expectation[Conditioned[ReducedSum]]).apply(Probability.Expect.ReducedSum.eq.ReducedSum.Expect)

    Eq << Probability.EqConditioned.of.Eq_Conditioned.independence_assumption.bidirectional.forget_histories.apply(Eq[0])

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(ReducedSum[Expectation]).apply(Probability.ReducedSum.Expect.eq.Expect.ReducedSum)

    # https://spinningup.openai.com/en/latest/spinningup/extra_pg_proof2.html



if __name__ == '__main__':
    run()
# created on 2023-04-10

from . import discounted
