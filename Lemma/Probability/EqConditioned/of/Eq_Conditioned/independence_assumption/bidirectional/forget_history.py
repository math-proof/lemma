from util import *


@apply
def apply(eq):
    ((r, t), ((s, (S[0], S[t])), S[s[:t].var])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    assert s.is_random and r.is_random
    assert t > 0
    return Equal(r[t:] | s[:t + 1], r[t:] | s[t])


@prove
def prove(Eq):
    from Lemma import Probability, Algebra

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t = Symbol(integer=True, positive=True) # time counter
    Eq << apply(
        Equal(r[t] | s[:t], r[t])) # history-irrelevant conditional independence assumption

    Eq << Probability.Eq.Conditioned.Infty.of.Eq_Conditioned.independence_assumption.apply(Eq[0])

    Eq << Algebra.Ne_0.of.Div1.gt.Zero.apply(Eq[0])

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1].this.find(Equal).apply(Algebra.Eq.Is.And.Eq.split)

    Eq << Probability.EqConditioned.of.Ne_0.Eq_Conditioned.joint.apply(Eq[-1], Eq[2])

    Eq << Eq[-1].this.find(Equal & Equal).apply(Algebra.Eq.Eq.Is.Eq.concat)




if __name__ == '__main__':
    run()
# created on 2023-04-05
