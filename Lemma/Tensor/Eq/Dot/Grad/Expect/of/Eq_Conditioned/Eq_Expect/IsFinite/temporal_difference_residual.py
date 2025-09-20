from util import *


@apply
def apply(eq, V_def, lt):
    from Lemma.Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, V_st_var = extract_QVA(eq, None, V_def, None, lt)
    At = r[t] + γ * V_st_var._subs(s[t].var, s[t + 1]) - V_st_var._subs(s[t].var, s[t])
    return Equal(γ ** Stack[t](t) @ Derivative[π](Expectation[r, a:π](r)),
                 γ ** Stack[t](t) @ Stack[t](Expectation[r, a:π, s](Derivative[π](log(Pr[a:π](a[t].surrogate | s[t].surrogate))) * At)))


@prove
def prove(Eq):
    from Lemma import Tensor, Probability

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation

    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    π = Symbol(shape=(D,), real=True) # trainable weights for the agent
    t = Symbol(integer=True) # time step counter
    V = Function(real=True, shape=()) # State-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    *Eq[-3:], Eq.hypothesis = apply(
                Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((V[π] ^ γ)(s[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Less(Sup[s[t].var, t](Abs(Derivative[π]((V[π] ^ γ)(s[t].var)))), oo))

    @Function(real=True, shape=())# Action-Value Function
    def Q(st, at, *limits):
        [π], [γ] = limits
        s_var, t = st.of(Indexed)
        a_var, S[t] = at.of(Indexed)
        assert s[t] != st and a[t] != at
        return γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | Equal(s[t], st) & Equal(a[t], at))
    Eq.Q_Function = (Q[π] ^ γ)(s[t].var, a[t].var).this.defun()

    @Function(real=True, shape=())
    def A(st, at, *limits): # Advantage Function
        [π], [γ] = limits
        return (Q[π] ^ γ)(st, at) - (V[π] ^ γ)(st)
    Eq.A_Function = (A[π] ^ γ)(s[t].var, a[t].var).this.defun()

    Eq << Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Eq_Sub.IsFinite.A_Function.apply(Eq[0], Eq.Q_Function, Eq[1], Eq.A_Function, Eq[2])

    Eq << Tensor.EqExpect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Eq_Sub.temporal_difference_residual.apply(Eq[0], Eq.Q_Function, Eq[1], Eq.A_Function).reversed

    Eq << Eq[-2].subs(Eq[-1].subs(s[t].var, s[t]).subs(a[t].var, a[t]))

    Eq << Eq[-1].this.find(Mul[Expectation]).apply(Probability.Mul.eq.Expect)

    Eq << Eq[-1].this.find(Expectation[Expectation]).apply(Probability.Expect.law_of_total_expectation)




if __name__ == '__main__':
    run()
# created on 2023-04-14
