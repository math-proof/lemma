from util import *


@apply
def apply(eq, Q_def, V_def, lt):
    from Lemma.Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var = extract_QVA(eq, Q_def, V_def, None, lt)
    return Equal(γ ** Stack[t](t) @ Derivative[π](Expectation[r, a:π](r)),
                 γ ** Stack[t](t) @ Stack[t](Expectation[a:π, s](Derivative[π](log(Pr[a:π](a[t].surrogate | s[t].surrogate))) * Q_st_var._subs(s[t].var, s[t])._subs(a[t].var, a[t]))))


@prove
def prove(Eq):
    from Lemma import Tensor, Calculus, Probability, Algebra, Discrete, Logic

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    π = Symbol(shape=(D,), real=True) # trainable weights for the agent
    t = Symbol(integer=True) # time step counter
    V, Q = Function(real=True, shape=()) # State-Value, Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    *Eq[-4:], Eq.hypothesis = apply(
                Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Less(Sup[s[t].var, t](Abs(Derivative[π]((V[π] ^ γ)(s[t].var)))), oo))

    n = Symbol(integer=True, nonnegative=True)
    Eq.expect = Tensor.Eq.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.apply(*Eq[:3], n)

    Eq << Calculus.EqLimit.of.Eq.apply(Eq.expect, (n, oo))

    Eq.limit = Eq[-1].this.find(Limit).apply(Calculus.Limit.eq.Add)

    Eq << Probability.AbsExpect.le.ExpectAbs.apply(Eq.limit.find(Expectation[Derivative]).subs(n, t))

    Eq << Probability.Expect.le.Sup.apply(Eq[-1].rhs)

    Eq.le_sup = Algebra.Le.of.Le.Le.apply(Eq[-2], Eq[-1])

    Eq << Algebra.All_Le_Sup.apply(Eq[3].lhs)

    Eq << Logic.All.of.Cond.apply(Eq[-1], s[t].var, simplify=None)

    Eq << Algebra.LeSup.of.All_Le.apply(Eq[-1])

    Eq << Algebra.Le.of.Le.Le.apply(Eq[-1], Eq.le_sup)

    Eq << Logic.All.of.Cond.apply(Eq[-1], t, simplify=None)

    Eq << Algebra.LeSup.of.All_Le.apply(Eq[-1])

    Eq << Algebra.Lt.of.Le.Lt.apply(Eq[3], Eq[-1])

    Eq << Eq[-1].this.lhs.limits_subs(t, n)

    Eq << Less(Abs(γ, evaluate=False), 1, plausible=True)

    Eq << Eq[-1].this.lhs.doit()

    Eq << Calculus.Eq_0.Limit.of.LtAbs.IsFinite.apply(Eq[-2], Eq[-1])

    Eq << Eq.limit.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Expectation[Sum]).apply(Probability.Expect.Sum.eq.Sum.Expect)

    Eq << Eq[-1].this.find(Limit).apply(Calculus.Limit.eq.Sum)

    Eq << Eq[-1].this.rhs.apply(Probability.Sum.Expect.eq.Expect.Sum)

    Eq << Eq[-1].this.find(Sum).apply(Tensor.Sum.eq.Dot, 1)

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.eq.Dot)

    Eq << Eq[-1].this.rhs.find(Expectation).apply(Probability.Expect.Stack.eq.Stack.Expect)

    Eq << Eq[-1].this.rhs.find(Stack).apply(Tensor.Stack.eq.Pow)

    # https://spinningup.openai.com/en/latest/spinningup/rl_intro.html# bellman-equations
    # http://incompleteideas.net/book/bookdraft2017nov5.pdf (Page 47)
    # https://lilianweng.github.io/posts/2018-04-08-policy-gradient/
    # https://danieltakeshi.github.io/2017/04/02/notes-on-the-generalized-advantage-estimation-paper/
    # https://spinningup.openai.com/en/latest/spinningup/rl_intro.html# id4
    # https://huggingface.co/deep-rl-course/unit4/pg-theorem?fw=pt
    # https://www.52coding.com.cn/tags/Reinforcement-Learning/
    # TRPO
    # https://arxiv.org/pdf/1502.05477.pdf




if __name__ == '__main__':
    run()
# created on 2023-03-30
# updated on 2023-04-14
