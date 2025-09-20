from util import *


@apply
def apply(eq, Q_def, V_def, MDV_def):
    from Lemma.Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var = extract_QVA(eq, Q_def, V_def)
    (((S[Q_st_var._subs(a[t].var, a[t])], S[s[t].as_boolean()]), (a, π_quote)), ((S[Pr[a:π_quote](a[t] | s[t])], S[Pr[a:π](a[t] | s[t])]), S[Pr[π, π_quote](s[t])], S[Pr[s:π](s[t])])), MDV_st_var = MDV_def.of(Equal[Expectation[Conditioned] - KL * Expr / Expr])

    return Equal(
        Subs[π_quote:π](Derivative[π_quote](MDV_st_var)),
        Expectation[a:π](
            Subs[π_quote:π](Derivative[π_quote](Pr[a:π_quote](a[t].surrogate | s[t]))) / Pr[a:π](a[t].surrogate | s[t]) * Q_st_var._subs(a[t].var, a[t]) | s[t]))


@prove
def prove(Eq):
    from Lemma import Probability, Calculus

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), integer=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t = Symbol(integer=True) # time step counter
    π = Symbol(shape=(D,), real=True, given=True) # trainable weights for the agent
    π_quote = Symbol(shape=(D,), real=True)
    π_hat = Symbol(r'\hat{π}', shape=(D,), real=True)
    π_tilde = Symbol(r"\tilde{π}", shape=(D,), real=True, given=True) # optimal weights for the new policy
    V, Q = Function(real=True, shape=()) # State-Value, Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True), given=True) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    MDV = Function(r'\mathcal{M}_\mathfrak{D}V', real=True, shape=())
    Eq << apply(Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Equal((MDV[π, π_quote] ^ γ)(s[t].var), Expectation[a:π_quote]((Q[π] ^ γ)(s[t].var, a[t]) | s[t]) - Pr[π, π_quote](s[t]) / Pr[s:π](s[t]) * KL(Pr[a:π_quote](a[t] | s[t]), Pr[a:π](a[t] | s[t]))))

    Eq << Eq[3].this.find(Expectation).apply(Probability.Expect.Conditioned.importance_sampling, π)

    Eq << Calculus.EqGrad.of.Eq.apply(Eq[-1], (π_quote,))

    Eq << Eq[-1].this.rhs.apply(Calculus.Grad.eq.Add)

    Eq << Eq[-1].this.find(Derivative[Expectation]).apply(Probability.Grad.Expect.eq.Expect.Grad)

    Eq << Eq[-1].this.find(Conditioned[~Derivative]).apply(Calculus.Grad.eq.Mul)

    Eq << Eq[-1].subs(π_quote, π)

    Eq << Eq[-1].this.rhs.find(Subs).apply(Probability.Subs_Grad_KL.eq.Zero)

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.limits.desimp)

    # https://arxiv.org/pdf/2201.02373.pdf
    # https://arxiv.org/pdf/2211.11030.pdf
    # https://arxiv.org/pdf/2205.01447.pdf
    # https://arxiv.org/pdf/2210.05639.pdf




if __name__ == '__main__':
    run()
# created on 2023-04-25
# updated on 2023-04-26
