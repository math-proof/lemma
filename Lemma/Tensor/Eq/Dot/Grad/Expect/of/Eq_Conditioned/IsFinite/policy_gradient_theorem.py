from util import *


@apply
def apply(eq, lt):
    ((r, t), (((a, (S[0], S[t])), S[a[:t].var]), ((s, (S[0], S[t])), S[s[:t].var]))), S[r[t]] = eq.of(Equal[Conditioned[Indexed, Equal[Sliced] & Equal[Sliced]]])
    assert a.is_random and s.is_random and r.is_random

    ((γ, (S[t], [S[t]])), (((S[r[t:]], S[s[t].as_boolean()]), (S[r[t:]],), (S[a], π)), [S[π], S[1]])), [S[s[t].var]], [S[t]] = lt.of(Sup[Abs[Pow[Stack] @ Derivative[Expectation[Conditioned]]]] < Infinity)
    return Equal(γ ** Stack[t](t) @ Derivative[π](Expectation[r, a:π](r)),
                 γ ** Stack[t](t) @ Stack[t](Expectation[r, a:π, s](Derivative[π](log(Pr[a:π](a[t].surrogate | s[t].surrogate))) * (γ ** Stack[t](t) @ r[t:]))))


@prove
def prove(Eq):
    from Lemma import Calculus, Tensor, Discrete, Probability, Algebra, Logic

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation

    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    π = Symbol(shape=(D,), real=True) # trainable weights for the agent
    t = Symbol(integer=True) # time step counter
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    *Eq[-2:], Eq.hypothesis = apply(
                Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Less(Sup[s[t].var, t](Abs(γ ** Stack[t](t) @ Derivative[π](Expectation[r[t:], a:π](r[t:] | s[t])))), oo))

    @Function(real=True, shape=())# Action-Value Function
    def Q(st, at, *limits):
        [π], [γ] = limits
        s_var, t = st.of(Indexed)
        a_var, S[t] = at.of(Indexed)
        assert s[t] != st and a[t] != at
        return γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | Equal(s[t], st) & Equal(a[t], at))
    Eq.Q_Function = (Q[π] ^ γ)(s[t].var, a[t].var).this.defun()

    @Function(real=True, shape=())# State-Value Function
    def V(st, *limits):
        [π], [γ] = limits
        s_var, t = st.of(Indexed)
        assert s[t] != st
        return γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | Equal(s[t], st))
    Eq.V_Function = (V[π] ^ γ)(s[t].var).this.defun()

    Eq << Eq[1].this.find(MatMul).apply(Calculus.Dot.Grad.eq.Grad.Dot)

    Eq << Eq[-1].subs(Eq.V_Function.reversed)

    Eq << Tensor.Eq.Dot.Grad.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.IsFinite.Q_Function.apply(Eq[0], Eq.Q_Function, Eq.V_Function, Eq[-1])

    Eq << Eq[-1].this.rhs.apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this.find(Mul[Expectation]).apply(Probability.Mul.eq.Expect)

    Eq.eq_expect = Eq[-1].this.rhs.apply(Probability.Sum.Expect.eq.Expect.Sum)

    Eq << Tensor.Eq.Expect.Grad.Log.Pr.of.Eq_Conditioned.Q_Function.discounted.apply(Eq[0], γ, t, π)

    Eq << Eq.Q_Function.subs(s[t].var, s[t]).subs(a[t].var, a[t])

    Eq << Eq[-2].subs(Eq[-1].reversed)

    Eq << Eq[-1] * γ ** t

    Eq << Eq[-1].this.lhs.apply(Probability.Mul.eq.Expect)

    Eq << Eq[-1].this.rhs.apply(Probability.Mul.eq.Expect)

    Eq << Algebra.EqSumS.of.Eq.apply(Eq[-1], (t, 0, oo))

    Eq << Eq[-1].this.rhs.apply(Probability.Sum.Expect.eq.Expect.Sum)

    Eq << Eq[-1].this.lhs.apply(Probability.Sum.Expect.eq.Expect.Sum)

    Eq << Logic.Eq.of.Eq.Eq.apply(Eq.eq_expect, Eq[-1])

    Eq << Eq[-1].this.find(Sum).apply(Tensor.Sum.eq.Dot, 1)

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.eq.Dot)

    Eq << Eq[-1].this.rhs.find(Stack).apply(Tensor.Stack.eq.Pow)

    Eq << Eq[-1].this.rhs.find(Expectation).apply(Probability.Expect.Stack.eq.Stack.Expect)

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
# created on 2023-04-07
# updated on 2023-04-14
