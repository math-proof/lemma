from util import *


@apply
def apply(Q_def):
    (γ, (discount, ((limit_rt, et), (S[limit_rt],), *weights))), Q_st_var = Q_def.of(Equal[(1 - Symbol) * MatMul[Expectation[Conditioned]]])
    r, (t, S[oo]) = limit_rt.of(Sliced)
    ((a, S[t]), S[a[t].var]), ((s, S[t]), S[s[t].var]) = et.of(Equal[Indexed] & Equal[Indexed])
    S[γ], (k, [S[k]]) = discount.of(Pow[Stack])

    assert a.is_random and s.is_random and r.is_random
    S[s[t].var], S[a[t].var], *S[weights], [S[γ]] = Q_st_var.of(Function)

    return Equal((1 - γ) * discount @ Expectation(r[t:] | s[t]), Expectation(Q_st_var._subs(a[t].var, a[t]) | s[t]))


@prove
def prove(Eq):
    from Lemma import Algebra, Probability, Calculus, Bool

    b = Symbol(integer=True, positive=True)
    s = Symbol(shape=(oo, b), real=True, random=True) # states / observation
    a = Symbol(shape=(oo,), integer=True, random=True) # actions
    r = Symbol(shape=(oo,), real=True, random=True) # rewards
    t, k = Symbol(integer=True) # time countor
    Q = Function(real=True, shape=()) # Action-Value Function
    γ = Symbol(domain=Interval(0, 1, left_open=True)) # Discount factor: penalty to uncertainty of future rewards; myopic for γ = 0; and far-sighted for γ = 1
    Eq << apply(Equal((Q ^ γ)(s[t].var, a[t].var), (1 - γ) * γ ** Stack[k](k) @ Expectation(r[t:] | s[t] & a[t])))

    Eq << Algebra.Ne_0.of.Div1.gt.Zero.apply(Eq[0])

    Eq << Probability.Ne_0.of.Ne_0.delete.apply(Eq[-1], 0)

    Eq << Eq[1].this.rhs.apply(Probability.Expect.eq.Sum)

    Eq << Eq[-1].subs(Eq[0])

    Eq << Bool.And_And.given.And.Cond.apply(Eq[-1])

    Eq << Eq[-1].this.rhs.find(Expectation).apply(Probability.Expect.eq.Integral)

    Eq << Eq[-1].this.find(Pow @ Integral).apply(Calculus.Dot.eq.Integral)

    Eq << Eq[-1].this.find(Mul[Integral]).apply(Calculus.Mul.eq.Integral)

    Eq << Eq[-1].this.find(Pr[2]).apply(Probability.Pr.Conditioned.eq.Div.Pr.Conditioned)

    Eq << Eq[-1].this.rhs.find(Sum).apply(Calculus.Sum.eq.Integral)

    Eq << Eq[-1].this.find(Sum[Pr]).apply(Probability.Sum.eq.Pr)

    Eq << Eq[-1].this.find(Expectation).apply(Probability.Expect.eq.Integral)

    Eq << Eq[-1].this.lhs.find(MatMul).apply(Calculus.Dot.eq.Integral)





if __name__ == '__main__':
    run()
# created on 2023-04-12
# updated on 2023-10-14
