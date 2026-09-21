from util import *


@apply
def apply(eq):
    ((r, t), ((s, (S[0], S[t])), S[s[:t].bvar])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    assert s.is_random and r.is_random
    assert t >= 0
    return Equal(r[t:] | s[:t + 1], r[t:] | s[t])


@prove
def prove(Eq):
    from Lemma import Random, Tensor

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t = Symbol(integer=True, positive=True) # time counter
    k = Symbol(integer=True, positive=True, given=False)
    Eq << apply(
        Equal(r[t] | s[:t], r[t])) # history-irrelevant conditional independence assumption

    Eq << Eq[0].this.domain_definition()

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1].this.find(Equal).apply(Tensor.Eq.Is.GetSlice.Get)

    Eq << Random.Eq.Conditioned.Infty.of.Eq_Conditioned.independence_assumption.apply(Eq[0])

    Eq << Random.ProbCond.of.Indep.Ne_0.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.find(And).apply(Tensor.Stack.UFn.Is.Stack)





if __name__ == '__main__':
    run()
# created on 2023-04-01
# updated on 2023-04-05
