from util import *


@apply
def apply(eq, Q_def, V_def, A_def, A_def_bar):
    from Lemma.Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var, A_st_var = extract_QVA(eq, Q_def, V_def, A_def)
    ((S[A_st_var._subs(a[t].var, a[t])], S[s[t].as_boolean()]), (S[a], π_quote)), A_st_var_bar = A_def_bar.of(Equal[Expectation[Conditioned]])
    assert π_quote.shape == π.shape
    return Equal(γ ** Stack[t](t) @ (Expectation[r, a:π_quote](r) - Expectation[r, a:π](r)),
                 γ ** Stack[t](t) @ Expectation(A_st_var_bar._subs(s[t].var, s)))


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Tensor

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation

    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    π, π_quote = Symbol(shape=(D,), real=True) # trainable weights for the agent
    t = Symbol(integer=True) # time step counter
    V, Q = Function(real=True, shape=()) # State-Value, Action-Value Function
    A = Function(real=True, shape=property(lambda self: self.arg.shape[:-1])) # Advantage Function
    γ = Symbol(domain=Interval(0, 1, right_open=True), given=True) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    *Eq[-5:], Eq.hypothesis = apply(
                Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Equal((A[π] ^ γ)(s[t].var, a[t].var), (Q[π] ^ γ)(s[t].var, a[t].var) - (V[π] ^ γ)(s[t].var)),
                Equal((A[π] ^ γ)(s[t].var), Expectation[a:π_quote]((A[π] ^ γ)(s[t].var, a[t]) | s[t])))

    Eq << Eq[-1].subs(s[t].var, s[t])

    Eq << Eq.hypothesis.this.rhs.find(Expectation).apply(Tensor.Expr.eq.Stack, t)

    Eq << Eq[-1].this.rhs.find(Expectation).subs(Eq[-2])

    Eq << Eq[-1].this.find(Expectation[Expectation]).apply(Probability.Expect.law_of_total_expectation)

    Eq << Tensor.EqDot.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Eq_Sub.A_Function.apply(*Eq[:4], π_quote)

    # https://arxiv.org/pdf/1502.05477.pdf#page=10




if __name__ == '__main__':
    run()
# created on 2023-04-12
# updated on 2023-04-14
