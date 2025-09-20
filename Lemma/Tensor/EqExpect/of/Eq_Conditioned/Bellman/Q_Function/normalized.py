from util import *


@apply
def apply(eq, γ=None, k=None, weights=None):
    ((r, t), (((a, (S[0], S[t])), S[a[:t].var]), ((s, (S[0], S[t])), S[s[:t].var]))), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced] & Equal[Sliced]]])
    if k is None:
        k = Symbol(integer=True) # time countor

    if γ is None:
        γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1

    assert s.is_random and r.is_random and a.is_random
    if weights:
        limits_curr = [(r[t:],), weights]
        limits_next = [(r[t + 1:],), weights]
        limits_coeff = [(r[t],), weights]
    else:
        limits_curr = []
        limits_next = []
        limits_coeff = []

    return Equal((1 - γ) * γ ** Stack[k](k) @ Expectation(r[t:] | s[t] & a[t], *limits_curr),
                 Expectation((γ * (1 - γ) * γ ** Stack[k](k) @ Expectation(r[t + 1:], *limits_next, given=Equal(s[t + 1], s[t + 1].surrogate)) + (1 - γ) * r[t]) | s[t] & a[t], *limits_coeff))


@prove
def prove(Eq):
    from Lemma import Tensor, Probability, Algebra

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t, k = Symbol(integer=True) # time countor
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    Eq << apply(
        Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
        γ, k)

    Eq << Tensor.EqExpect.of.Eq_Conditioned.Bellman.Q_Function.apply(Eq[0], γ)

    Eq << Eq[-1] * (1 - γ)

    Eq << Eq[-1].this.rhs.apply(Probability.Mul.eq.Expect)

    Eq << Eq[-1].this.rhs.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS, i=1)

    print()


if __name__ == '__main__':
    run()
# created on 2023-04-12
