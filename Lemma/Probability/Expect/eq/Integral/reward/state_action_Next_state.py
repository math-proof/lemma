from util import *


@apply
def apply(self):
    ((r, t), (((a, S[t]), S[a[t].var]), ((s, S[t]), S[s[t].var]), S[s[t + 1].as_boolean()])), (S[r[t]],) = self.of(Expectation[Conditioned[Indexed, Equal[Indexed] & Equal[Indexed]]])
    assert s.is_random and a.is_random and r.is_random
    return Equal(self, Integral[r[t].var](r[t].var * Pr(s[t + 1] & r[t], given=s[t] & a[t]) / Pr(s[t + 1] | s[t] & a[t])))



@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Logic

    b = Symbol(integer=True, positive=True)
    # states / observation of the agent
    s = Symbol(shape=(oo, b), real=True, random=True)
    # actions to take by the agent
    a = Symbol(shape=(oo,), integer=True, random=True)
    # rewards from the environment
    r = Symbol(shape=(oo,), real=True, random=True)
    # discrete time step
    t = Symbol(integer=True)
    Eq << apply(Expectation[r[t]](r[t] | s[t] & a[t] & s[t + 1]))

    Eq << Logic.Cond.given.Imp.domain_defined.apply(Eq[0])

    Eq << Eq[-1].this.lhs.apply(Probability.Ne_0.Conditioned.of.Ne_0, a[t], s[t])

    Eq << Eq[-1].this.lhs.apply(Probability.Eq.of.Ne_0.bayes.Conditioned, r[t])

    Eq << Logic.Imp.given.Imp.subst.apply(Eq[-1])

    Eq << Eq[-1].this.find(Expectation).apply(Probability.Expect.eq.Integral)

    # the expected rewards for state–action–next-state triples as a three-argument function r
    # http://incompleteideas.net/book/bookdraft2017nov5.pdf (Eq. 3.6)




if __name__ == '__main__':
    run()
# created on 2023-03-27
# updated on 2023-11-18
