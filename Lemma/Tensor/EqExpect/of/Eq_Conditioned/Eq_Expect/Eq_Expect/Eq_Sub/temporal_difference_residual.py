from util import *


@apply
def apply(eq, Q_def, V_def, A_def):
    from Lemma.Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman import extract_QVA
    s, a, r, *weights, γ, t, Q_st_var, V_st_var, A_st_var = extract_QVA(eq, Q_def, V_def, A_def)

    [π], = weights
    return Equal(Expectation[r[t], s[t + 1], a:π](r[t] + γ * V_st_var._subs(s[t].var, s[t + 1]) - V_st_var, given=s[t] & a[t]), A_st_var)


@prove
def prove(Eq):
    from Lemma import Probability, Tensor

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    π = Symbol(shape=(D,), real=True) # trainable weights for the agent
    t = Symbol(integer=True) # time step counter
    V, Q, A = Function(real=True, shape=()) # State-Value, Action-Value, Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    Eq << apply(Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Equal((A[π] ^ γ)(s[t].var, a[t].var), (Q[π] ^ γ)(s[t].var, a[t].var) - (V[π] ^ γ)(s[t].var)))

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Add)

    Eq << Eq[-1] + Eq[-3]

    Eq << Eq[-1].reversed.simplify()

    Eq << Eq[-1].this.rhs.apply(Probability.Add.Expect.eq.Expect)

    Eq << Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman.apply(*Eq[:3])[-1]

    # https://arxiv.org/pdf/1506.02438.pdf#page=4




if __name__ == '__main__':
    run()
# created on 2023-04-13
# updated on 2023-04-27
