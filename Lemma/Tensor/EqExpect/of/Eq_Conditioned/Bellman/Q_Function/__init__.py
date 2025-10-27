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
        limits_coeff = [(r[t],), (s[t + 1],), weights]
    else:
        limits_curr = []
        limits_next = []
        limits_coeff = []

    return Equal(γ ** Stack[k](k) @ Expectation(r[t:] | s[t] & a[t], *limits_curr),
                 Expectation((γ * γ ** Stack[k](k) @ Expectation(r[t + 1:], *limits_next, given=Equal(s[t + 1], s[t + 1].surrogate)) + r[t]) | s[t] & a[t], *limits_coeff))


@prove
def prove(Eq):
    from Lemma import Probability, Calculus, Tensor, Algebra, Rat

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t, k = Symbol(integer=True) # time countor
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    Eq << apply(
        Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
        γ, k)

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.eq.Add)

    Eq << Eq[-1].this.find(Expectation[2]).apply(Probability.Expect.eq.Integral)

    Eq << Eq[-1].this.find(Integral[Mul]).apply(Calculus.Integral.eq.Mul)

    Eq.final = Eq[-1].this.lhs.apply(Probability.Dot.eq.Expect)

    Eq << Eq.final.lhs.this.find(MatMul).apply(Tensor.Dot.eq.Add.Mul.Dot.discounted_future_reward)

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.eq.Add)

    Eq.eq_add = Eq[-1].this.find(Expectation[Conditioned[Mul]]).apply(Probability.Expect.eq.Mul)

    Eq << Eq.eq_add.find(Mul[~Expectation]).this.apply(Probability.Expect.eq.Integral)

    Eq << Eq[-1].this.find(Pr).apply(Probability.Pr.eq.Integral.joint, s[t + 1])

    Eq << Eq[-1].this.find(Mul[Integral]).apply(Calculus.Mul.eq.Integral)

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.limits.swap)

    Eq << Eq[-1].this.find(Pr).apply(Probability.Pr.Conditioned.eq.Mul.Pr.Conditioned)

    Eq.eq_expect = Eq[-1].this.rhs.apply(Calculus.Integral.limits.separate)

    Eq << Rat.Ne_0.of.Div1.gt.Zero.apply(Eq[0]).subs(t, t + 1)

    Eq << Probability.Ne_0.of.Ne_0.joint_slice.apply(Eq[-1], [t, slice(t, t + 2)])

    Eq << Eq[-1].this.find(Equal[Sliced]).apply(Algebra.Eq.Is.And.Eq.split)

    Eq << Probability.EqConditioned.of.Eq_Conditioned.joint.independence_assumption.apply(Eq[0])

    Eq << Probability.EqConditioned.of.Ne_0.Eq_Conditioned.joint.apply(*Eq[-2:])

    Eq << Eq.eq_expect.subs(Eq[-1])

    Eq << Eq.final.rhs.find(MatMul).this.apply(Probability.Dot.eq.Expect)

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.eq.Integral)

    Eq << Eq[-3].subs(Eq[-1].reversed)

    Eq << Eq.eq_add.subs(Eq[-1])

    # http://incompleteideas.net/book/bookdraft2017nov5.pdf (Bellman equation Eq. 3.14)
    # http://incompleteideas.net/book/RLbook2020.pdf
    # http://incompleteideas.net/book/the-book-2nd.html




if __name__ == '__main__':
    run()
# created on 2023-03-29
# updated on 2023-10-14
from . import normalized
