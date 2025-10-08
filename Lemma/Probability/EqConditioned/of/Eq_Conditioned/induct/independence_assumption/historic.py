from util import *


@apply
def apply(eq, k):
    ((r, t), ((s, (S[0], S[t])), S[s[:t].var])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    assert s.is_random and r.is_random
    assert k >= 0 and t >= 0
    return Equal(r[t + k] | s[:t], r[t + k])


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Bool

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t = Symbol(integer=True, positive=True) # time counter
    k = Symbol(integer=True, nonnegative=True, given=False)
    Eq << apply(Equal(r[t] | s[:t], r[t]), k) # history-irrelevant conditional independence assumption

    Eq << Eq[1].subs(k, 0)

    Eq.induct = Eq[1].subs(k, k + 1)

    Eq << Eq[1].subs(t, t + 1)

    Eq << Eq[-1].this.find(Equal).apply(Algebra.Eq.Is.And.Eq.split)

    Eq << Probability.EqConditioned.of.Eq_Conditioned.getitem.apply(Eq[-1], s[:t])

    Eq << Imply(Eq[1], Eq.induct, plausible=True)

    Eq << Bool.Eq.of.Eq.All_Imp.apply(Eq[0], Eq[-1], k, start=0)





if __name__ == '__main__':
    run()
# created on 2023-04-01
# updated on 2023-04-05
