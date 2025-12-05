from util import *


def extract_QVA(eq, Q_def=None, V_def=None, A_def=None, lt_dV=None):
    ((r, t), (((a, (S[0], S[t])), S[a[:t].var]), ((s, (S[0], S[t])), S[s[:t].var]))), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced] & Equal[Sliced]]])

    if Q_def is not None:
        (discount, ((S[r[t:]], S[s[t] & a[t]]), (S[r[t:]],), *weights)), Q_st_var = Q_def.of(Equal[MatMul[Expectation[Conditioned]]])
        if V_def is not None:
            (S[discount], ((S[r[t:]], S[s[t].as_boolean()]), (S[r[t:]],), *S[weights])), V_st_var = V_def.of(Equal[MatMul[Expectation[Conditioned]]])
        else:
            V_st_var = None
    else:
        (discount, ((S[r[t:]], S[s[t].as_boolean()]), (S[r[t:]],), *weights)), V_st_var = V_def.of(Equal[MatMul[Expectation[Conditioned]]])
        Q_st_var = None

    if A_def is not None:
        (S[Q_st_var], S[V_st_var]), A_st_var = A_def.of(Equal[Expr - Expr])
    else:
        A_st_var = None

    γ, (S[t], [S[t]]) = discount.of(Pow[Stack])
    assert a.is_random and s.is_random and r.is_random

    (S[a], π), = weights
    weights = [(π,),]

    funcs = []

    if Q_st_var:
        S[s[t].var], S[a[t].var], *S[weights], [S[γ]] = Q_st_var.of(Function)
        funcs.append(Q_st_var)

    if V_st_var:
        S[s[t].var], *S[weights], [S[γ]] = V_st_var.of(Function)
        funcs.append(V_st_var)

        if lt_dV is not None:
            S[Derivative[π](V_st_var)], [S[s[t].var]], [S[t]] = lt_dV.of(Sup[Abs] < Infinity)

    if A_st_var:
        S[s[t].var], S[a[t].var], *S[weights], [S[γ]] = A_st_var.of(Function)
        funcs.append(A_st_var)

    return s, a, r, *weights, γ, t, *funcs

@apply
def apply(eq, Q_def, V_def):
    s, a, r, [π], γ, t, Q_st_var, V_st_var = extract_QVA(eq, Q_def, V_def)
    V_st = V_st_var._subs(s[t].var, s[t + 1])
    return Equal(V_st_var, Expectation[a[t]:π](Q_st_var._subs(a[t].var, a[t]) | s[t])),\
        Equal(V_st_var, Expectation[r[t], s[t + 1], a:π]((r[t] + γ * V_st) | s[t])), \
        Equal(Q_st_var, Expectation[r[t], s[t + 1], a:π]((r[t] + γ * V_st) | s[t] & a[t]))


@prove
def prove(Eq):
    from Lemma import Tensor, Bool, Probability

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    π = Symbol(shape=(D,), real=True) # trainable weights for the agent
    t = Symbol(integer=True) # time step counter
    V, Q = Function(real=True, shape=()) # State-Value, Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    Eq << apply(Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])))

    Eq << Tensor.EqExpect.of.Eq_Expect.V_Function.apply(Eq[1])

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[2], Eq[-1])

    Eq << Probability.EqConditioned.of.Eq_Conditioned.getitem.apply(Eq[0], 1)

    Eq << Tensor.EqExpect.of.Eq_Conditioned.Bellman.V_Function.apply(Eq[-1], γ, t, (a, π))

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[2], Eq[-1])

    Eq << Eq[2].subs(t, t + 1)

    Eq.v_next = Eq[-1].subs(s[t + 1].var, s[t + 1])

    Eq << Eq[-2].subs(Eq.v_next.reversed)

    Eq << Tensor.EqExpect.of.Eq_Conditioned.Bellman.Q_Function.apply(Eq[0], γ, t, (a, π))

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].subs(Eq.v_next.reversed)

    # https://spinningup.openai.com/en/latest/spinningup/rl_intro.html# bellman-equations
    # http://incompleteideas.net/book/bookdraft2017nov5.pdf (Page 47)
    # https://lilianweng.github.io/posts/2018-04-08-policy-gradient/
    # https://spinningup.openai.com/en/latest/spinningup/rl_intro.html# id4
    # https://huggingface.co/deep-rl-course/unit4/pg-theorem?fw=pt
    # https://www.52coding.com.cn/tags/Reinforcement-Learning/
    # TRPO
    # https://arxiv.org/pdf/1502.05477.pdf




if __name__ == '__main__':
    run()
# created on 2023-03-28
# updated on 2023-04-27
from . import normalized
from . import optimality
