from util import *


@apply
def apply(eq):
    ((r, t), ((s, (S[0], S[t])), S[s[:t].var])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    assert s.is_random and r.is_random
    assert t >= 0
    return Equal(r[t:] | s[:t], r[t:])


@prove
def prove(Eq):
    from Lemma import Probability

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t = Symbol(integer=True, positive=True) # time counter
    k = Symbol(integer=True, positive=True, given=False)
    Eq << apply(
        Equal(r[t] | s[:t], r[t])) # history-irrelevant conditional independence assumption

    Eq << Probability.EqConditioned.of.Eq_Conditioned.induct.independence_assumption.future.apply(Eq[0], oo)





if __name__ == '__main__':
    run()
# created on 2023-04-01
# updated on 2023-04-05
