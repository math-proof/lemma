from util import *


@apply
def apply(eq, Q_def, V_def, A_def, π_quote=None):
    from Lemma.Tensor.And.Eq.Expect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Bellman import extract_QVA
    s, a, r, [π], γ, t, Q_st_var, V_st_var, A_st_var = extract_QVA(eq, Q_def, V_def, A_def)
    assert π_quote.shape == π.shape
    return Equal(γ ** Stack[t](t) @ (Expectation[r, a:π_quote](r) - Expectation[r, a:π](r)),
                 γ ** Stack[t](t) @ Stack[t](Expectation[a:π_quote, s]((A_st_var._subs(s[t].var, s[t])._subs(a[t].var, a[t])))))


@prove
def prove(Eq):
    from Lemma import Tensor, Probability, Discrete, Algebra

    b, D = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    π, π_quote = Symbol(shape=(D,), real=True) # trainable weights for the agent
    t = Symbol(integer=True) # time step counter
    V, Q, A = Function(real=True, shape=()) # State-Value Function, Action-Value Function, Advantage Function
    γ = Symbol(domain=Interval(0, 1, right_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    *Eq[-4:], Eq.hypothesis = apply(
                Equal(r[t] | s[:t] & a[:t], r[t]), # history-irrelevant conditional independence assumption for rewards based on states and actions
                Equal((Q[π] ^ γ)(s[t].var, a[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t] & a[t])),
                Equal((V[π] ^ γ)(s[t].var), γ ** Stack[t](t) @ Expectation[r[t:], a:π](r[t:] | s[t])),
                Equal((A[π] ^ γ)(s[t].var, a[t].var), (Q[π] ^ γ)(s[t].var, a[t].var) - (V[π] ^ γ)(s[t].var)),
                π_quote)

    Eq << Tensor.EqExpect.of.Eq_Conditioned.Eq_Expect.Eq_Expect.Eq_Sub.temporal_difference_residual.apply(*Eq[:4]).reversed

    Eq << Eq[-1].subs(s[t].var, s[t]).subs(a[t].var, a[t])

    Eq << Eq.hypothesis.subs(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Stack).apply(Probability.Stack.Expect.eq.Expect.Stack)

    Eq << Eq[-1].this.rhs.apply(Probability.Dot.eq.Expect)

    Eq << Eq[-1].this.rhs.find(MatMul).apply(Tensor.Dot.eq.Sum)

    Eq << Eq[-1].this.rhs.find(Mul[Expectation]).apply(Probability.Mul.eq.Expect)

    Eq << Eq[-1].this.find(Mul[Add]).apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.find(Symbol * Pow).args[:2].apply(Algebra.Mul.eq.Pow.Add.exponent)

    Eq << Eq[-1].this.rhs.find(Sum[~Expectation]).apply(Probability.Expect.eq.Add)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Algebra.Sum_Add.eq.AddSumS)

    Eq << Eq[-1].this.rhs.find(Expectation[Conditioned[Pow * Function]]).apply(Probability.Expect.eq.Mul)

    Eq << Eq[-1].this.rhs.apply(Probability.Expect.eq.Add)

    Eq << Eq[-1].this.find(Expectation[-Sum]).apply(Probability.Expect.eq.Mul)

    Eq << Eq[-1].this.find(Expectation[Sum[Expectation]]).apply(Probability.Expect.Sum.eq.Sum.Expect)

    Eq << Eq[-1].this.find(Sum[~Expectation]).simplify()

    Eq << Eq[-1].this.find(Sum[~Expectation]).apply(Probability.Expect.law_of_total_expectation)

    Eq << Eq[-1].this.find(Sum[Expectation]).apply(Probability.Sum.Expect.eq.Expect.Sum)

    Eq << Eq[-1].this.find(Expectation[~Sum]).apply(Tensor.Sum.eq.Dot)

    Eq << Eq[-1].this.find(Expectation[MatMul]).apply(Probability.Expect.eq.Dot)

    Eq << Eq[-1].this.find(Expectation[Sum]).apply(Probability.Expect.Sum.eq.Sum.Expect)

    Eq << Eq[-1].this.find(Sum[~Expectation]).apply(Probability.Expect.eq.Mul)

    Eq << Eq[-1].this.find(Sum[Mul[~Expectation]]).simplify()

    Eq << Eq[-1].this.find(Sum[Mul[~Expectation]]).apply(Probability.Expect.law_of_total_expectation)

    Eq << Eq[-1].this.find(Sum).apply(Algebra.Sum.limits.subst.offset, -1)

    Eq << Eq[-1].this.find(Expectation[Sum]).apply(Probability.Expect.Sum.eq.Sum.Expect)

    Eq << Eq[-1].this.find(Sum[~Expectation]).apply(Probability.Expect.eq.Mul)

    Eq << Eq[-1].this.find(-~Sum).apply(Algebra.Sum.eq.Add.shift)

    Eq << Eq[2].subs(s[t].var, s[t]).subs(t, 0)

    Eq << Eq[-2].subs(Eq[-1])

    Eq << Eq[-1].this.find(Expectation[MatMul]).apply(Probability.Expect.eq.Dot)

    Eq << Eq[-1].this.find(Expectation[Expectation]).apply(Probability.Expect.law_of_total_expectation)

    Eq << Eq[-1].this.rhs.find(MatMul[~Stack]).apply(Tensor.Stack.eq.Pow)

    Eq << Eq[-1].this.rhs.apply(Tensor.Add.eq.Dot)

    # https://arxiv.org/pdf/1502.05477.pdf#page=10




if __name__ == '__main__':
    run()
# created on 2023-04-12
# updated on 2023-05-20
