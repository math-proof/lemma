from util import *


@apply
def apply(eq, Q_def, V_def, MDV_def, any, eq_argmax):
    from Lemma.Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var = extract_QVA(eq, Q_def, V_def)
    (((S[Q_st_var._subs(a[t].var, a[t])], S[s[t].as_boolean()]), (a, π_quote)), ((S[Pr[a:π_quote](a[t] | s[t])], S[Pr[a:π](a[t] | s[t])]), S[Pr[π, π_quote](s[t])], S[Pr[s:π](s[t])])), MDV_st_var = MDV_def.of(Equal[Expectation[Conditioned] - KL * Expr / Expr])
    ((S[MDV_st_var._subs(s[t].var, s[t])._subs(t, 0)], (s, π)), [S[π_quote]]), π_tilde = eq_argmax.of(Equal[ArgMax[Expectation]])

    return V_st_var._subs(π, π_tilde) >= V_st_var, \
        γ ** Stack[t](t) @ Expectation[r, a:π_tilde](r) >= γ ** Stack[t](t) @ Expectation[r, a:π](r)


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Set, Bool

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
    *Eq[-6:], (Eq.ge_VF, Eq.ge_reward) = apply(Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Equal((MDV[π, π_quote] ^ γ)(s[t].var), Expectation[a:π_quote]((Q[π] ^ γ)(s[t].var, a[t]) | s[t]) - Pr[π, π_quote](s[t]) / Pr[s:π](s[t]) * KL(Pr[a:π_quote](a[t] | s[t]), Pr[a:π](a[t] | s[t]))),
                Exists[π_hat](And(
                    Equal(Pr[a:π_hat](a[0] | s[0]), Piecewise((Pr[a:π](a[0] | s[0]), Equal(s[0].var, s[t].var)), (Pr[a:π_quote](a[0] | s[0]), True))),
                    Equal(Pr[π, π_hat](s[0]), Piecewise((Pr[π, π](s[0]), Equal(s[0].var, s[t].var)), (Pr[π, π_quote](s[0]), True))))),
                Equal(π_tilde, ArgMax[π_quote](Expectation[s:π]((MDV[π, π_quote] ^ γ)(s[0])))))

    Eq << Algebra.Ne_0.of.Div1.gt.Zero.apply(Eq[3])

    Eq.ne_zero = Eq[-1].subs(t, 0)

    Eq << Algebra.All.Ge.of.Eq_ArgMax.apply(Eq[5])

    Eq << Eq[-1].subs(π_quote, π_hat)

    Eq << Algebra.Ge_0.of.Ge.apply(Eq[-1])

    Eq << Eq[-1].this.lhs.apply(Probability.Add.Expect.eq.Expect)

    Eq << Eq[-1].this.lhs.simplify()

    Eq << Eq[-1].this.lhs.apply(Probability.Expect.eq.Sum)

    Eq.ge_sum = Eq[-1].this.lhs.apply(Algebra.Sum.eq.AddSumS, cond={s[t].var})

    Eq.infer = Imply(
        And(Equal(Pr[a:π_hat](a[0] | s[0]), Pr[a:π_tilde](a[0] | s[0])), Equal(Pr[π, π_hat](s[0]), Pr[π, π_tilde](s[0]))),
        Equal((MDV[π, π_tilde] ^ γ)(s[0].var) - (MDV[π, π_hat] ^ γ)(s[0].var), 0),
        plausible=True)

    Eq << Eq[3].subs(t, 0)

    Eq <<= Eq[-1].subs(π_quote, π_tilde), Eq[-1].subs(π_quote, π_hat), Eq[-1].subs(π_quote, π)

    Eq.MDV_pi_tilde, Eq.MDV_pi_hat, Eq.MDV_pi = Eq[-3].this.find(Expectation).apply(Probability.Expect.eq.Sum), Eq[-2].this.find(Expectation).apply(Probability.Expect.eq.Sum), Eq[-1].this.find(Expectation).apply(Probability.Expect.eq.Sum)

    Eq << Eq.infer.subs(Eq.MDV_pi_tilde, Eq.MDV_pi_hat)

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1], slice(None, 2))

    Eq << Bool.Imp_And.given.Imp.And.subst.apply(Eq[-1], 0)

    Eq << Bool.Imp_And.given.Imp.And.subst.apply(Eq[-1], 1)

    Eq << Algebra.Ne_0.of.Div1.gt.Zero.apply(Eq[0])

    Eq << Eq[4].this.find(Equal[Piecewise]).apply(Bool.And.Imp.of.Cond_Ite)

    Eq << Eq[-1].this.find(Equal[Piecewise]).apply(Bool.And.Imp.of.Cond_Ite)

    Eq << Eq[-1].this.expr.apply(Algebra.And.of.And.delete, 1)

    Eq << Eq[-1].this.expr.args[1:].apply(Bool.ImpAndS.of.Imp.Imp)

    Eq << Eq[-1].subs(π_quote, π_tilde)

    Eq << Bool.Any_And.of.Any.All.apply(Eq[-1], Eq.infer)

    Eq.any = Eq[-1].this.expr.args[1:].apply(Bool.Imp.of.Imp.Imp)

    Eq << Eq.ge_sum.this.find(Sum).apply(Algebra.Sum.eq.Sum_MulBool)

    Eq << Eq[-1].this.find(Element).apply(Set.In_SDiff.Is.And)

    Eq << Eq[-1].this.find(NotElement).simplify()

    Eq << Eq[-1].this.find(functions.Bool).apply(Bool.Bool.eq.Ite)

    Eq << Eq.any.this.find(Imply[2]).apply(Bool.EqIteS.of.Imp_Eq, Eq[-1].find(Piecewise))

    Eq << Bool.Any_And.of.Any.All.apply(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.expr.args[:2].apply(Bool.Cond.of.Eq.Cond.subst)

    Eq << Bool.And_And.of.And.apply(Eq.ne_zero)[1].subs(s[0].var, s[t].var)

    Eq << Algebra.Gt_0.of.Ne_0.apply(Eq[-1])

    Eq << Bool.Any_And.of.Any.All.apply(Eq[-1], Eq[-3])

    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.GeDiv.of.Gt_0.Ge)

    Eq << Eq[-1].this.find(GreaterEqual).apply(Algebra.Ge.of.Ge_0)

    Eq.ge_MDV = GreaterEqual((MDV[π, π_tilde] ^ γ)(s[t].var), (MDV[π, π] ^ γ)(s[t].var), plausible=True)

    Eq << ~Eq.ge_MDV

    Eq << Algebra.Any.And.of.Any.Any.apply(Eq[-1], Eq[-2])

    Eq << Eq[-1].this.expr.args[:2].apply(Algebra.Lt.of.Ge.Lt)

    Eq << Eq[-1].this.find(Imply).apply(Bool.ImpEq.of.ImpEq.subst)

    Eq << Eq[-1].subs(s[0].var, s[t].var)

    Eq << Eq.MDV_pi.subs(s[0].var, s[t].var)

    Eq << Eq.MDV_pi_hat.subs(s[0].var, s[t].var)

    Eq << Eq[-3].subs(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.expr.apply(Bool.Cond.of.Eq.Cond.subst)

    Eq << Eq[3].subs(π_quote, π_tilde)

    Eq << Eq[-1].this.find(Expectation).apply(Probability.Expect.limits.desimp)

    Eq << Probability.And.Ge.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Eq_Expect.Ge.drift.apply(*Eq[:3], Eq[-1], Eq.ge_MDV)

    # https://arxiv.org/pdf/2201.02373.pdf
    # https://arxiv.org/pdf/2211.11030.pdf
    # https://arxiv.org/pdf/2205.01447.pdf
    # https://arxiv.org/pdf/2210.05639.pdf




if __name__ == '__main__':
    run()
# created on 2023-04-24
# updated on 2023-05-15
