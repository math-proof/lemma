from util import *


@apply
def apply(ne_zero_lhs, ne_zero_rhs, y):
    (x_lhs, x_var), *weights_lhs = ne_zero_lhs.of(Unequal[Pr[Equal], 0])
    (x_rhs, S[x_var]), *weights_rhs = ne_zero_rhs.of(Unequal[Pr[Equal], 0])

    return GreaterEqual(KL(Pr(Equal(x_lhs, x_var) & Equal(y, y.var), *weights_lhs), Pr(Equal(x_rhs, x_var) & Equal(y, y.var), *weights_rhs)),
                        KL(Pr(Equal(x_lhs, x_var), *weights_lhs), Pr(Equal(x_rhs, x_var), *weights_rhs)))

@prove
def prove(Eq):
    from Lemma import Probability, Algebra, Calculus, Real


    D, m, n = Symbol(integer=True, positive=True)
    θ, θ_quote = Symbol(real=True, shape=(D,))
    x = Symbol(random=True, real=True, shape=(m,))
    y = Symbol(random=True, real=True, shape=(n,))
    Eq << apply(Unequal(Pr[θ](x), 0),
                Unequal(Pr[θ_quote](x), 0), y)

    Eq << Eq[-1].this.find(KL).apply(Probability.KL.eq.Integral, order=lambda s : str(s))

    Eq << Eq[-1].this.find(KL).apply(Probability.KL.eq.Integral)

    Eq << Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq[0], y, spread_weight=True)

    Eq << Probability.Pr.eq.Mul.Pr.of.Ne_0.bayes.apply(Eq[1], y, spread_weight=True)

    Eq << Eq[-3].subs(Eq[-2], Eq[-1])

    Eq << Eq[-1].this.lhs.find(Log).apply(Real.LogMul.eq.AddLogS, pivot=2)

    Eq << Eq[-1].this.lhs.expr.apply(Algebra.Mul_Add.eq.AddMulS)

    Eq << Eq[-1].this.lhs.apply(Calculus.Integral.eq.Add)

    Eq << Eq[-1].this.lhs.args[1].apply(Calculus.Integral.limits.swap)

    Eq << Eq[-1].this.lhs.args[1].apply(Calculus.Integral.limits.separate)

    Eq << Eq[-1].this.find(Integral[Pr[Conditioned]]).apply(Probability.Integral.eq.One.Conditioned)

    Eq << Eq[-1].this.lhs.apply(Calculus.Integral.limits.swap)

    Eq << Eq[-1].this.lhs.apply(Calculus.Integral.limits.separate)

    Eq << Eq[-1].this.find(Integral[Mul[~Integral]]).apply(Probability.Integral.eq.KL)

    Eq << Probability.KLPrSConditioned.ge.Zero.apply(*Eq[-1].find(KL).args)

    Eq << Algebra.Ge_0.Mul.of.Ge_0.apply(Eq[-1], Pr[θ](Equal(x, x.var)))

    Eq << Calculus.Ge_0.Integral.of.Ge_0.apply(Eq[-1], (x.var,))





if __name__ == '__main__':
    run()
# created on 2023-03-25
# updated on 2023-03-26
