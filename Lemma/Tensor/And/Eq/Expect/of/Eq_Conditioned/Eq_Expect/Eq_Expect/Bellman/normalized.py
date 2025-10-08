from util import *


def extract_QVA(eq, Q_def, V_def=None):
    ((r, t), (((a, (S[0], S[t])), S[a[:t].var]), ((s, (S[0], S[t])), S[s[:t].var]))), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced] & Equal[Sliced]]])

    (γ, (discount, ((S[r[t:]], S[s[t] & a[t]]), [S[r[t:]]], *weights))), Q_st_var = Q_def.of(Equal[(1 - Symbol) * MatMul[Expectation[Conditioned]]])

    if V_def is not None:
        (S[γ], (S[discount], ((S[r[t:]], S[s[t].as_boolean()]), [S[r[t:]]], *S[weights]))), V_st_var = V_def.of(Equal[(1 - Symbol) * MatMul[Expectation[Conditioned]]])
    else:
        V_st_var = None

    S[γ], (S[t], [S[t]]) = discount.of(Pow[Stack])
    assert a.is_random and s.is_random and r.is_random

    if weights:
        (S[a], π), = weights
        weights = [(π,),]

    S[s[t].var], S[a[t].var], *S[weights], [S[γ]] = Q_st_var.of(Function)

    if V_st_var:
        if weights:
            S[s[t].var], *S[weights] = V_st_var.of(Function)
        else:
            S[s[t].var], [S[γ]] = V_st_var.of(Function)

    return s, a, r, *weights, γ, t, Q_st_var, V_st_var

@apply
def apply(eq, Q_def, V_def):
    s, a, r, *weights, γ, t, Q_st_var, V_st_var = extract_QVA(eq, Q_def, V_def)

    if weights:
        [π], = weights
        limits_Q = [(a[t], π)]
        limits_V = [(r[t],), (s[t + 1],), (a, π)]
    else:
        limits_Q = limits_V = []

    V_st = V_st_var._subs(s[t].var, s[t + 1])
    return Equal(V_st_var, Expectation(Q_st_var._subs(a[t].var, a[t]) | s[t], *limits_Q)),\
        Equal(V_st_var, Expectation(((1 - γ) * r[t] + γ * V_st) | s[t], *limits_V)), \
        Equal(Q_st_var, Expectation(((1 - γ) * r[t] + γ * V_st) | s[t] & a[t], *limits_V))


@prove
def prove(Eq):
    from Lemma import Tensor, Algebra, Probability, Bool

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t = Symbol(integer=True) # time step counter
    V, Q = Function(real=True, shape=()) # State-Value, Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    Eq << apply(Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q ^ γ)(s[t].var, a[t].var), (1 - γ) * γ ** Stack[t](t) @ Expectation(r[t:] | s[t] & a[t])),
                Equal((V ^ γ)(s[t].var), (1 - γ) * γ ** Stack[t](t) @ Expectation(r[t:] | s[t])))

    Eq << Tensor.EqExpect.of.Eq_Expect.V_Function.normalized.apply(Eq[1])

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[2], Eq[-1])

    Eq << Probability.EqConditioned.of.Eq_Conditioned.getitem.apply(Eq[0], 1)

    Eq << Tensor.EqExpect.of.Eq_Conditioned.Bellman.V_Function.normalized.apply(Eq[-1], γ, t)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[2], Eq[-1])

    Eq << Eq[2].subs(t, t + 1)

    Eq.v_next = Eq[-1].subs(s[t + 1].var, s[t + 1])

    Eq << Eq[-2].subs(Eq.v_next.reversed)

    Eq << Tensor.EqExpect.of.Eq_Conditioned.Bellman.Q_Function.normalized.apply(Eq[0], γ, t)

    Eq << Bool.Eq.of.Eq.Eq.apply(Eq[1], Eq[-1])

    Eq << Eq[-1].subs(Eq.v_next.reversed)


if __name__ == '__main__':
    run()
# created on 2023-04-12
