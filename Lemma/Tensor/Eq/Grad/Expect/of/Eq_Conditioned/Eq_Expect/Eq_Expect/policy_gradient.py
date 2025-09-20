from util import *


@apply
def apply(eq, Q_def, V_def, n=None):
    from Lemma.Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var = extract_QVA(eq, Q_def, V_def)
    assert n >= 0
    return Equal(γ ** Stack[t](t) @ Derivative[π](Expectation[r, a:π](r)),
                 Expectation[a:π, s[:n]](Sum[t:n](γ ** t * Derivative[π](log(Pr[a:π](a[t].surrogate | s[t].surrogate))) * Q_st_var._subs(s[t].var, s[t])._subs(a[t].var, a[t]))) + \
                 γ ** n * Expectation(Derivative[π](V_st_var._subs(s[t].var, s[n]))))




@prove
def prove(Eq):
    from Lemma import Probability, Calculus, Tensor, Algebra

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    π = Symbol(shape=(D,), real=True) # trainable weights for the agent
    t = Symbol(integer=True) # time step counter
    V, Q = Function(real=True, shape=()) # State-Value, Action-Value Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    n = Symbol(integer=True, nonnegative=True, given=False)
    *Eq[-3:], Eq.hypothesis = apply(
                Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])), n)

    Eq << Eq[2].subs(t, 0)

    Eq << Eq[-1].subs(s[0].var, s[0])

    Eq << Probability.EqExpect.of.Eq.apply(Eq[-1])

    Eq << Eq[-1].this.find(MatMul).apply(Probability.Dot.eq.Expect)

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.law_of_total_expectation)

    Eq << Calculus.EqGrad.of.Eq.apply(Eq[-1], [π])

    Eq << Eq[-1].this.lhs.apply(Probability.Grad.Expect.eq.Expect.Grad).reversed

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.eq.Integral)

    Eq << Tensor.EqGrad.of.Eq_Conditioned.Eq_Expect.Eq_Expect.policy_gradient.induct.apply(*Eq[:3], n)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.rhs.apply(Calculus.Integral.eq.Add)

    Eq << Eq[-1].this.find(Mul[Sum]).apply(Algebra.Mul_Sum.eq.Sum_Mul)

    Eq << Eq[-1].this.find(Integral[Sum]).apply(Calculus.Integral.eq.Sum)

    Eq << Eq[-1].this.find(Integral[Mul]).apply(Calculus.Integral.eq.Mul)

    Eq << Eq[-1].this.find(Sum[~Integral[Mul]]).apply(Calculus.Integral.eq.Mul)

    Eq << Eq[-1].this.find(Integral[~Mul[Integral]]).apply(Calculus.Mul.eq.Integral)

    Eq << Eq[-1].this.find(Integral[~Mul[Integral]]).apply(Calculus.Mul.eq.Integral)

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.limits.concat)

    Eq << Eq[-1].this.find(Sum[Mul[~Integral]]).apply(Calculus.Integral.limits.concat)

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.limits.pop.Slice)

    Eq << Eq[-1].this.rhs.find(Sum)().find(Integral).apply(Calculus.Integral.limits.pop.Slice)

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.limits.separate)

    Eq << Eq[-1].this.find(Derivative * ~Integral).apply(Probability.Integral.Prod.eq.Pr)

    Eq << Eq[-1].this.find(Integral).apply(Probability.Integral.eq.Expect)

    Eq << Eq[-1].this.find(Integral).apply(Calculus.Integral.limits.separate)

    Eq << Eq[-1].this.find(Integral[Pr * Product]).apply(Probability.Integral.Prod.eq.Pr)

    Eq << Eq[-1].this.find(Derivative[Pr]).apply(Calculus.Grad.eq.Mul.Grad.Log)

    Eq << Eq[-1].this.find(Pr * ~Sum).apply(Probability.Sum.eq.Expect)

    Eq << Eq[-1].this.find(Integral).apply(Probability.Integral.eq.Expect)

    Eq << Eq[-1].this.find(Expectation[Expectation]).apply(Probability.Expect.law_of_total_expectation)

    Eq << Eq[-1].this.find(Sum[~Mul[Expectation]]).apply(Probability.Mul.eq.Expect)

    Eq << Eq[-1].this.find(Sum[Expectation]).apply(Probability.Sum.Expect.eq.Expect.Sum)

    Eq << Eq[-1].this.lhs.find(Expectation).apply(Probability.Expect.eq.Dot)

    Eq << Eq[-1].this.lhs.apply(Calculus.Grad.Dot.eq.Dot.Grad)

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
# created on 2023-04-04
# updated on 2023-04-12
