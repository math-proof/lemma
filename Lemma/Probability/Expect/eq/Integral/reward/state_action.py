from util import *


@apply
def apply(self):
    ((r, t), (((a, S[t]), S[a[t].var]), ((s, S[t]), S[s[t].var]))), (S[r[t]],) = self.of(Expectation[Conditioned[Indexed, Equal[Indexed] & Equal[Indexed]]])
    assert s.is_random and a.is_random and r.is_random
    return Equal(self, Integral[r[t].var](r[t].var * Integral[s[t + 1].var](Pr(s[t + 1] & r[t], given=s[t] & a[t]))))



@prove
def prove(Eq):
    from Lemma import Probability

    b = Symbol(integer=True, positive=True)
    # states / observation of the agent
    s = Symbol(shape=(oo, b), real=True, random=True)
    # actions to take by the agent
    a = Symbol(shape=(oo,), integer=True, random=True)
    # rewards from the environment
    r = Symbol(shape=(oo,), real=True, random=True)
    # discrete time step
    t = Symbol(integer=True)
    Eq << apply(Expectation[r[t]](r[t] | s[t] & a[t]))

    Eq << Integral[s[t + 1].var](Pr(s[t + 1] & r[t], given=s[t] & a[t])).this.apply(Probability.Integral.eq.Pr.marginal)

    Eq << Eq[0].this.lhs.apply(Probability.Expect.eq.Integral)

    Eq << Eq[-1].subs(Eq[-2].reversed)

    # the expected rewards for state–action pairs as a two-argument function r
    # http://incompleteideas.net/book/bookdraft2017nov5.pdf (Eq. 3.5)




if __name__ == '__main__':
    run()
# created on 2023-03-27
# updated on 2023-11-18
