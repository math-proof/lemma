from util import *


@apply
def apply(eq):
    ((r, t), (((a, (S[0], S[t])), S[a[:t].var]), ((s, (S[0], S[t])), S[s[:t].var]))), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced] & Equal[Sliced]]])
    # assert t >= 0
    assert s.is_random and r.is_random and a.is_random
    return Equal(r[t + 1:] | s[t] & a[t], r[t + 1:])


@prove
def prove(Eq):
    from Lemma import Random, Rat, Tensor

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t = Symbol(integer=True, positive=True) # time counter
    k = Symbol(integer=True, positive=True, given=False)
    Eq << apply(
        Equal(r[t] | s[:t] & a[:t], r[t])) # history-irrelevant conditional independence assumption

    Eq << Random.EqConditioned.of.Eq_Conditioned.getitem.apply(Eq[0])

    Eq << Random.Eq.Conditioned.Infty.of.Eq_Conditioned.independence_assumption.apply(Eq[-1])

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1].this.find(Equal).apply(Tensor.Eq.Is.And.Eq.split)

    Eq.eq_at = Random.EqConditioned.of.Eq_Conditioned.getitem.apply(Eq[-1], 0)

    Eq << Random.EqConditioned.of.Eq_Conditioned.getitem.apply(Eq[0], 1)

    Eq << Random.Eq.Conditioned.Infty.of.Eq_Conditioned.independence_assumption.apply(Eq[-1])

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1].this.find(Equal).apply(Tensor.Eq.Is.And.Eq.split)

    Eq.eq_st = Random.EqConditioned.of.Eq_Conditioned.getitem.apply(Eq[-1], 0)

    Eq << Rat.Ne_0.of.Div1.gt.Zero.apply(Eq[0])

    Eq << Eq[-1].subs(t, t + 1)

    Eq << Eq[-1].this.find(Equal).apply(Tensor.Eq.Is.And.Eq.split)

    Eq << Eq[-1].this.find(Equal[3]).apply(Tensor.Eq.Is.And.Eq.split)

    Eq << Random.Ne_0.of.Ne_0.delete.apply(Eq[-1], slice(2, None))

    Eq << Random.EqConditioned.of.Ne_0.Eq_Conditioned.Eq_Conditioned.joint.apply(Eq[-1], Eq.eq_at, Eq.eq_st)





if __name__ == '__main__':
    run()
# created on 2023-04-05
# updated on 2023-05-20
