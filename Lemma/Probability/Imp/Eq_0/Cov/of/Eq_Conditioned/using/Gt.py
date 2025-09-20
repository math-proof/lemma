from util import *


@apply
def apply(eq, i, swap=False):
    ((r, t), ((s, (S[0], S[t])), S[s[:t].var])), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced]]])
    # assert t >= 0
    assert s.is_random and r.is_random
    if swap:
        s, r = r, s
    return Imply(t > i, Equal(Covariance(r[t], s[i]), Zeros(*r[t].shape).outer_product(Zeros(*s[i].shape))))


@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Logic

    s, r = Symbol(shape=(oo,), real=True, random=True)
    t, i = Symbol(integer=True) # time counter
    Eq << apply(
        Equal(r[t] | s[:t], r[t]), i) # history-irrelevant conditional independence assumption

    Eq << Probability.All.Eq_Conditioned.of.Eq_Conditioned.independence_assumption.apply(Eq[0], i)

    Eq << Eq[-1].this.expr.apply(Probability.Eq_0.Cov.of.Eq_Conditioned, swap=True)

    Eq << Logic.Imp.given.All.apply(Eq[1], i)

    Eq << Algebra.All.given.All.limits.domain_defined.apply(Eq[-1])




if __name__ == '__main__':
    run()
# created on 2023-04-19
