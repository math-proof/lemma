from util import *


@apply
def apply(eq, Q_def, V_def, Q_star_def, V_star_def):
    from Lemma.Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var = extract_QVA(eq, Q_def, V_def)

    (S[Q_st_var], [S[π]]), Q_star_st_var = Q_star_def.of(Equal[Maxima])
    (S[V_st_var], [S[π]]), V_star_st_var = V_star_def.of(Equal[Maxima])

    limits_V = [(r[t],), (s[t + 1],)]

    V_star_st = V_star_st_var._subs(s[t].var, s[t + 1])

    return Equal(V_star_st_var, Maxima[a[t].var](Q_star_st_var)),\
        Equal(V_star_st_var, Expectation((r[t] + γ * V_star_st) | s[t], *limits_V)), \
        Equal(Q_star_st_var, Expectation((r[t] + γ * V_star_st) | s[t] & a[t], *limits_V))

@prove(proved=False)
def prove(Eq):
    from Lemma import Tensor

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    π = Symbol(shape=(D,), real=True) # trainable weights for the agent
    t = Symbol(integer=True) # time step counter
    V, Q = Function(real=True, shape=()) # State-Value, Action-Value Function
    V_star, Q_star = Function(real=True, shape=()) # optimal State-Value, Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    Eq << apply(
                Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Equal((Q_star ^ γ)(s[t].var, a[t].var), Maxima[π]((Q[π] ^ γ)(s[t].var, a[t].var))),
                Equal((V_star ^ γ)(s[t].var), Maxima[π]((V[π] ^ γ)(s[t].var))))

    Eq << Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman.apply(*Eq[:3])

    Eq << Eq[3].subs(Eq[-1])

    # https://spinningup.openai.com/en/latest/spinningup/rl_intro.html# bellman-equations
    # http://incompleteideas.net/book/RLbook2020.pdf#page=85



if __name__ == '__main__':
    run()
# created on 2023-04-26
# updated on 2023-10-03
