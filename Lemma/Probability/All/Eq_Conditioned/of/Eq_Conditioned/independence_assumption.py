from util import *


@apply
def apply(eq, i):
    ((r, t), ((s, (S[0], S[t])), S[s[:t].var])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    # assert t >= 0
    assert s.is_random and r.is_random
    return All[i:t](Equal(r[t] | s[i], r[t]))


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Set, Bool

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t = Symbol(integer=True) # time counter
    i = Symbol(integer=True)
    Eq << apply(
        Equal(r[t] | s[:t], r[t]), i) # history-irrelevant conditional independence assumption

    Eq << Probability.EqConditioned.of.Eq_Conditioned.independence_assumption.future.apply(Eq[0])

    j = Symbol(integer=True, nonnegative=True)
    Eq << Eq[2][j]

    Eq << Bool.All.of.Cond.apply(Eq[-1], j)

    Eq << Eq[-1].this.apply(Algebra.All.limits.subst.offset, -1)

    Eq << Eq[-1].this.apply(Algebra.All.limits.subst.offset, -t)

    j = Eq[-1].variable
    Eq << Bool.Imp.of.AllSetOf.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.reversed

    Eq << Eq[-1].this.lhs.apply(Algebra.Le.given.Lt.One)

    Eq << Eq[-1].subs(t, i)

    Eq << Eq[-1].subs(j, t)



    Eq << Bool.All.given.Imp.apply(Eq[1])

    Eq << Eq[-1].this.find(Element).apply(Set.Lt.of.In_Ico)




if __name__ == '__main__':
    run()
# created on 2023-04-19
