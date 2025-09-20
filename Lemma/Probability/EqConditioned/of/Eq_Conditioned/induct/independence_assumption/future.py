from util import *


@apply
def apply(eq, k):
    ((r, t), ((s, (S[0], S[t])), S[s[:t].var])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    assert s.is_random and r.is_random
    assert k > 0 and t >= 0
    return Equal(r[t:t + k] | s[:t], r[t:t + k])


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Logic

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t = Symbol(integer=True, nonnegative=True) # time counter
    k = Symbol(integer=True, positive=True, given=False)
    Eq << apply(
        Equal(r[t] | s[:t], r[t]), k) # history-irrelevant conditional independence assumption

    Eq << Eq[1].subs(k, 1)

    Eq.induct = Eq[1].subs(k, k + 1)

    Eq << Probability.EqConditioned.of.Eq_Conditioned.induct.independence_assumption.historic.apply(Eq[0], k)

    Eq << Probability.EqPr.of.Eq_Conditioned.Eq_Conditioned.joint.apply(Eq[1], Eq[2])

    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.Eq.Is.Eq.concat)

    Eq << Eq[-1].this.find(And).apply(Algebra.Eq.Eq.Is.Eq.concat)

    Eq << Imply(Eq[1], Eq.induct, plausible=True)

    Eq << Logic.Eq.of.Eq.All_Imp.apply(Eq[0], Eq[-1], k, start=1)





if __name__ == '__main__':
    run()
# created on 2023-04-01
# updated on 2023-04-05
